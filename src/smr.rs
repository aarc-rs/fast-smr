use std::alloc::Layout;
use std::cell::{RefCell, UnsafeCell};
use std::collections::VecDeque;
use std::mem;
use std::mem::zeroed;
use std::ptr::{null_mut, NonNull};
use std::sync::atomic::Ordering::{Relaxed, SeqCst};
use std::sync::atomic::{AtomicPtr, AtomicU64};

use crate::utils::ULL;

const SLOTS_PER_NODE: usize = 8;

pub struct Reclaimer {
    slots: ULL<Slot, SLOTS_PER_NODE>,
    epoch: AtomicU64,
    tag: AtomicU64,
}

impl Reclaimer {
    pub const fn new() -> Self {
        unsafe { zeroed() }
    }

    pub fn claim_slot(&self, cleanup_freq: usize) -> ThreadContext<'_> {
        let slot = self.slots.apply(Slot::try_claim);
        ThreadContext {
            reclaimer: self,
            slot,
            cleanup_freq,
            cleanup_counter: 0,
            limbo_list: unsafe {
                if let Some(b) = mem::take(&mut *slot.limbo_list.get()) {
                    b.into_vec()
                } else {
                    Vec::default()
                }
            },
            counts: RefCell::new(Default::default()),
            snapshot_intervals: vec![],
            snapshot_ptrs: vec![],
        }
    }

    pub fn current_epoch(&self) -> u64 {
        self.epoch.load(SeqCst)
    }
}

impl Default for Reclaimer {
    fn default() -> Self {
        Self::new()
    }
}

struct Slot {
    start_epoch: AtomicU64,
    end_epoch: AtomicU64,
    help_ptr: AtomicPtr<AtomicPtr<u8>>,
    hazard_ptr: AtomicPtr<u8>,

    limbo_list: UnsafeCell<Option<Box<[RetiredFn]>>>,
}

impl Slot {
    const UNCLAIMED: u64 = u64::MAX;
    const NO_RESERVE: u64 = u64::MAX - 1;

    const fn new() -> Self {
        Self {
            start_epoch: AtomicU64::new(Self::NO_RESERVE),
            end_epoch: AtomicU64::new(Self::UNCLAIMED),
            help_ptr: AtomicPtr::new(null_mut()),
            hazard_ptr: AtomicPtr::new(null_mut()),
            limbo_list: UnsafeCell::new(None),
        }
    }

    fn try_claim(&self) -> bool {
        self.end_epoch
            .compare_exchange(Self::UNCLAIMED, Self::NO_RESERVE, SeqCst, Relaxed)
            .is_ok()
    }
}

impl Default for Slot {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Send for Slot {}
unsafe impl Sync for Slot {}

pub struct ThreadContext<'a> {
    reclaimer: &'a Reclaimer,
    slot: &'a Slot,

    cleanup_freq: usize,
    cleanup_counter: usize,

    limbo_list: Vec<RetiredFn>,

    // a monotonically increasing queue consisting of (epoch, count) tuples.
    counts: RefCell<VecDeque<(u64, usize)>>,

    // reusable lists for storing snapshots when scanning slots during retirement.
    snapshot_intervals: Vec<(u64, u64)>,
    snapshot_ptrs: Vec<*mut u8>,
}

impl<'a> ThreadContext<'a> {
    pub fn load<T>(&mut self, src: &AtomicPtr<T>, attempts: usize) -> Option<Guard<'a, '_, T>> {
        match NonNull::new(src.load(SeqCst)) {
            Some(initial) => self.protect(src, initial, attempts),
            None => None,
        }
    }

    fn protect<T>(
        &mut self,
        src: &AtomicPtr<T>,
        initial: NonNull<T>,
        attempts: usize,
    ) -> Option<Guard<'a, '_, T>> {
        let mut counts = self.counts.borrow_mut();
        let mut ptr = initial;
        let mut curr_epoch = self.reclaimer.epoch.load(SeqCst);
        let mut initial_end_epoch = Slot::NO_RESERVE;

        // if curr_epoch was already protected, simply increment the count in our local tracker.
        if let Some(back) = counts.back_mut() {
            initial_end_epoch = back.0;
            if initial_end_epoch == curr_epoch {
                back.1 += 1;
                return Some(Guard {
                    ctx: self,
                    epoch: curr_epoch,
                    ptr,
                });
            }
        }

        // set end_epoch to curr_epoch in accordance with 2GEIBR
        self.slot.end_epoch.store(curr_epoch, SeqCst);

        // try the fast path
        for _ in 0..attempts {
            ptr = match NonNull::new(src.load(SeqCst)) {
                Some(p) => p,
                None => {
                    // null ptrs don't need protection. reset end_epoch to what it was originally.
                    self.slot.end_epoch.store(initial_end_epoch, SeqCst);
                    return None;
                }
            };
            self.slot.end_epoch.store(curr_epoch, SeqCst);

            let reloaded_epoch = self.reclaimer.epoch.load(SeqCst);
            if curr_epoch == reloaded_epoch {
                if counts.is_empty() {
                    // this is our first reservation, so start_epoch must also be updated.
                    self.slot.start_epoch.store(curr_epoch, SeqCst);
                }
                counts.push_back((curr_epoch, 1));
                return Some(Guard {
                    ctx: self,
                    epoch: curr_epoch,
                    ptr,
                });
            }
            curr_epoch = reloaded_epoch;
        }

        // fall back to the slow path. first, publish the parent block.
        let help = src as *const _ as *const () as *mut AtomicPtr<u8>;
        self.slot.help_ptr.store(help, SeqCst);

        // set the low bit to signal that we need help
        let tag = (self.reclaimer.tag.fetch_add(1, SeqCst) << 1) | 1;
        self.slot.hazard_ptr.store(tag as *mut _, SeqCst);

        // load the target ourselves
        let mut loaded_ptr = src.load(SeqCst);

        // publish the hazardous pointer, or check to see if anyone helped us
        if let Err(helped) = self.slot.hazard_ptr.compare_exchange(
            tag as *mut _,
            loaded_ptr as *mut _,
            SeqCst,
            SeqCst,
        ) {
            loaded_ptr = helped as *mut _;
        }

        // similar to the above case, null pointers don't need protection.
        ptr = match NonNull::new(loaded_ptr) {
            Some(p) => p,
            None => {
                self.slot.hazard_ptr.store(null_mut(), SeqCst); // clear the help flag
                self.slot.end_epoch.store(initial_end_epoch, SeqCst);
                return None;
            }
        };

        // protect the current epoch; the target is guaranteed to be alive during this epoch
        // because we already protected it using the hazard pointer
        curr_epoch = self.reclaimer.epoch.load(SeqCst);
        self.slot.end_epoch.store(curr_epoch, SeqCst);
        self.slot.hazard_ptr.store(null_mut(), SeqCst); // clear the help flag
        if counts.is_empty() {
            // this is our first reservation, so start_epoch must also be updated.
            self.slot.start_epoch.store(curr_epoch, SeqCst);
        }
        counts.push_back((curr_epoch, 1));
        Some(Guard {
            ctx: self,
            epoch: curr_epoch,
            ptr,
        })
    }

    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn retire(
        &mut self,
        ptr: *mut u8,
        layout: Layout,
        f: unsafe fn(*mut u8, Layout),
        birth_epoch: u64,
    ) {
        self.cleanup_counter = (self.cleanup_counter + 1) % self.cleanup_freq;
        let retire_epoch = if self.cleanup_counter == 0 {
            self.scan_and_cleanup();
            self.reclaimer.epoch.fetch_add(1, SeqCst)
        } else {
            self.reclaimer.epoch.load(SeqCst)
        };
        let span = (birth_epoch, retire_epoch);
        self.limbo_list.push(RetiredFn {
            ptr,
            layout,
            f,
            span,
        });
    }

    #[allow(clippy::missing_safety_doc)]
    unsafe fn scan_and_cleanup(&mut self) {
        // scan all slots.
        for slot in self.reclaimer.slots.into_iter() {
            let end = slot.end_epoch.load(SeqCst);
            if end == Slot::UNCLAIMED || end == Slot::NO_RESERVE {
                continue;
            }
            let mut start = slot.start_epoch.load(SeqCst);
            if start == Slot::NO_RESERVE {
                // this slot has one reservation, defined by end_epoch.
                start = end;
            }
            self.snapshot_intervals.push((start, end));

            // helping procedure
            let loaded = slot.hazard_ptr.load(SeqCst);
            if loaded.is_null() {
                continue;
            } else if loaded as usize & 1 == 1 {
                // if the low bit is set, they need help
                let help_ptr = slot.help_ptr.load(SeqCst);
                self.slot.hazard_ptr.store(help_ptr as *mut _, SeqCst);
                if slot.hazard_ptr.load(SeqCst) == loaded {
                    // make sure it didn't change. if it did, they no longer need help.
                    let tgt = (*help_ptr).load(SeqCst);
                    _ = slot
                        .hazard_ptr
                        .compare_exchange(loaded, tgt, SeqCst, Relaxed);
                    self.snapshot_ptrs.push(tgt as *mut _);
                }
                self.slot.hazard_ptr.store(null_mut(), SeqCst);
            } else {
                self.snapshot_ptrs.push(loaded as *mut _);
            }
        }

        /*
        // merge the intervals.
        if self.snapshot_intervals.len() > 1 {
            self.snapshot_intervals.sort_unstable();
            let mut i = 1;
            for j in 1..self.snapshot_intervals.len() {
                let (start, end) = self.snapshot_intervals[j];
                // [(1, 2), (3, 4)] can be merged into [(1, 4)].
                if start <= self.snapshot_intervals[i - 1].1 + 1 {
                    self.snapshot_intervals[i - 1].1 = max(end, self.snapshot_intervals[i - 1].1);
                } else {
                    self.snapshot_intervals[i] = (start, end);
                    i += 1;
                }
            }
            self.snapshot_intervals.truncate(i);
        }
        */

        let mut i = 0;
        while i < self.limbo_list.len() {
            let mut has_conflict = self
                .snapshot_intervals
                .iter()
                .any(|x| intervals_overlap(self.limbo_list[i].span, *x));
            for snapshot_ptr in self.snapshot_ptrs.iter() {
                let block_start = self.limbo_list[i].ptr as usize;
                let block_end = block_start + self.limbo_list[i].layout.size();
                let hazard_addr = *snapshot_ptr as usize;
                has_conflict |= (block_start <= hazard_addr) && (hazard_addr < block_end);
                if has_conflict {
                    break;
                }
            }
            if has_conflict {
                i += 1;
            } else {
                self.limbo_list.swap_remove(i);
            }
        }

        self.snapshot_intervals.clear();
        self.snapshot_ptrs.clear();
    }
}

impl<'a> Drop for ThreadContext<'a> {
    fn drop(&mut self) {
        unsafe {
            self.scan_and_cleanup();
            *self.slot.limbo_list.get() = Some(mem::take(&mut self.limbo_list).into_boxed_slice());
        }
        self.slot.end_epoch.store(Slot::UNCLAIMED, SeqCst);
    }
}

fn intervals_overlap(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 <= b.1 && b.0 <= a.1
}

pub struct Guard<'a: 'b, 'b, T> {
    ctx: &'b ThreadContext<'a>,
    ptr: NonNull<T>,
    epoch: u64,
}

impl<'a: 'b, 'b, T> AsRef<T> for Guard<'a, 'b, T> {
    fn as_ref(&self) -> &T {
        unsafe { &(*self.ptr.as_ptr()) }
    }
}

impl<'a: 'b, 'b, T> Drop for Guard<'a, 'b, T> {
    fn drop(&mut self) {
        let mut counts = self.ctx.counts.borrow_mut();
        debug_assert_ne!(counts.len(), 0);

        // decrement the count.
        let pair = counts.iter_mut().find(|(e, _)| *e == self.epoch).unwrap();
        debug_assert!(pair.1 > 0);
        pair.1 -= 1;

        let mut start_epoch_changed = false;
        let mut end_epoch_changed = false;
        // pop from the front and back of the queue to shrink the interval.
        while let Some((_, count)) = counts.front() {
            if *count > 0 {
                break;
            }
            counts.pop_front();
            start_epoch_changed = true;
        }
        while let Some((_, count)) = counts.back() {
            if *count > 0 {
                break;
            }
            counts.pop_back();
            end_epoch_changed = true;
        }

        if counts.is_empty() {
            // we have no more reservations; zero out our interval.
            self.ctx.slot.end_epoch.store(Slot::NO_RESERVE, SeqCst);
            self.ctx.slot.start_epoch.store(Slot::NO_RESERVE, SeqCst);
        } else {
            if start_epoch_changed {
                self.ctx
                    .slot
                    .start_epoch
                    .store(counts.front().unwrap().0, SeqCst);
            }
            if end_epoch_changed {
                self.ctx
                    .slot
                    .end_epoch
                    .store(counts.back().unwrap().0, SeqCst);
            }
        }
    }
}

struct RetiredFn {
    ptr: *mut u8,
    layout: Layout,
    f: unsafe fn(*mut u8, Layout),
    span: (u64, u64),
}

impl Drop for RetiredFn {
    fn drop(&mut self) {
        unsafe {
            (self.f)(self.ptr, self.layout);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::{dealloc, Layout};
    use std::ptr::null_mut;
    use std::sync::atomic::Ordering::SeqCst;
    use std::sync::atomic::{AtomicPtr, AtomicUsize};
    use std::{array, thread};

    use crate::smr::Reclaimer;

    // Test struct to be allocated on the heap.
    pub struct Block {
        birth_epoch: u64,
        data: usize,
    }

    impl Block {
        const LAYOUT: Layout = Layout::new::<Self>();

        fn alloc(reclaimer: &Reclaimer, val: usize) -> *mut Self {
            Box::into_raw(Box::new(Block {
                birth_epoch: reclaimer.current_epoch(),
                data: val,
            }))
        }
    }

    #[test]
    fn test_concurrent_reader_writer() {
        const UPDATES: usize = 50;
        const READERS: usize = 4;

        let reclaimer = Reclaimer::new();
        let shared_ptr = AtomicPtr::new(Block::alloc(&reclaimer, 0));
        let reads_completed = AtomicUsize::new(0);

        thread::scope(|scope| {
            // Writer thread: continuously updates the value
            scope.spawn(|| unsafe {
                let mut ctx = reclaimer.claim_slot(5);
                for i in 1..=UPDATES {
                    let new_val = Block::alloc(&reclaimer, i);
                    let old = shared_ptr.swap(new_val, SeqCst);
                    if !old.is_null() {
                        ctx.retire(old as *mut _, Block::LAYOUT, dealloc, (*old).birth_epoch);
                    }
                }
            });

            // Reader threads: continuously read and verify monotonic increases
            for _ in 0..READERS {
                scope.spawn(|| {
                    let mut ctx = reclaimer.claim_slot(1);
                    let mut last_seen = 0;
                    let mut local_reads = 0;

                    while last_seen < UPDATES {
                        if let Some(guard) = ctx.load(&shared_ptr, 1) {
                            let val = guard.as_ref().data;
                            // Values should never decrease
                            assert!(
                                val >= last_seen,
                                "Non-monotonic read: {} after {}",
                                val,
                                last_seen
                            );
                            last_seen = val;
                            local_reads += 1;
                        }
                    }

                    reads_completed.fetch_add(local_reads, SeqCst);
                });
            }
        });

        // Clean up the final value
        let last = shared_ptr.load(SeqCst);
        unsafe {
            assert_eq!((*last).data, UPDATES);
            dealloc(last as *mut _, Block::LAYOUT);
        }

        println!("Total reads completed: {}", reads_completed.load(SeqCst));
        println!("Epoch increments: {}", reclaimer.epoch.load(SeqCst));
    }

    #[test]
    fn test_protect_retire_miri() {
        basic_test_1::<5, 100>();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_protect_retire_no_miri() {
        basic_test_1::<64, 200>();
    }

    fn basic_test_1<const THREADS: usize, const MAX_VAL: usize>() {
        // basic test:
        // result: each thread swaps x, incrementing results[x.swap(...)] by 1.
        let results: [AtomicUsize; MAX_VAL] = array::from_fn(|_| AtomicUsize::new(0));
        let reclaimer = Reclaimer::new();

        let x: AtomicPtr<Block> = AtomicPtr::default();

        let logic = || {
            let mut ctx = reclaimer.claim_slot(1);
            for val in 0..MAX_VAL {
                if let Some(guard) = ctx.load(&x, 1) {
                    assert!(guard.as_ref().data < MAX_VAL);
                }
                let new_item = Block::alloc(&reclaimer, val);
                let old = x.swap(new_item, SeqCst);
                if !old.is_null() {
                    unsafe {
                        results[(*old).data].fetch_add(1, SeqCst);
                        // immediately retire the object we swapped out
                        ctx.retire(old as *mut u8, Block::LAYOUT, dealloc, (*old).birth_epoch);
                    }
                }
            }
        };

        // spawn some threads to run the logic concurrently
        thread::scope(|scope| {
            for _ in 0..THREADS {
                scope.spawn(logic);
            }
        });

        // there's still one object stored in x, clean it up for testing purposes
        let last = x.swap(null_mut(), SeqCst);
        unsafe {
            results[(*last).data].fetch_add(1, SeqCst);
            dealloc(last as *mut u8, Block::LAYOUT);
        }

        // check the result array to make sure the counts are correct
        for item in results.iter() {
            assert_eq!(item.load(SeqCst), THREADS);
        }

        println!("Epoch increments: {}", reclaimer.epoch.load(SeqCst));
    }
}
