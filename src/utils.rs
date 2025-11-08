use std::array::from_fn;
use std::ptr::null_mut;
use std::sync::atomic::AtomicPtr;
use std::sync::atomic::Ordering::{Relaxed, SeqCst};

// A specialized lock-free unrolled linked list.
#[repr(C)]
#[allow(clippy::upper_case_acronyms)]
pub(crate) struct ULL<T, const N: usize> {
    head: ULLNode<T, N>,
}

impl<T: Default, const N: usize> ULL<T, N> {
    pub(crate) fn apply<F: Fn(&T) -> bool>(&self, f: F) -> &T {
        let mut curr = &self.head;
        loop {
            for item in &curr.items {
                if f(item) {
                    return item;
                }
            }
            curr = curr.get_or_init_next();
        }
    }
}

#[repr(C)]
struct ULLNode<T, const N: usize> {
    items: [T; N],
    next: AtomicPtr<Self>,
}

impl<T: Default, const N: usize> ULLNode<T, N> {
    pub(crate) fn get_or_init_next(&self) -> &Self {
        unsafe {
            let next = self.next.load(SeqCst);
            if !next.is_null() {
                return &*next;
            }
            let new_node = Box::into_raw(Box::new(Self {
                items: from_fn(|_| T::default()),
                next: AtomicPtr::default(),
            }));
            match self
                .next
                .compare_exchange(null_mut(), new_node, SeqCst, SeqCst)
            {
                Ok(_) => &*new_node,
                Err(existing) => {
                    drop(Box::from_raw(new_node));
                    &*existing
                }
            }
        }
    }
}

impl<T, const N: usize> Drop for ULLNode<T, N> {
    fn drop(&mut self) {
        let next = self.next.load(Relaxed);
        if !next.is_null() {
            unsafe {
                drop(Box::from_raw(next));
            }
        }
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a ULL<T, N> {
    type Item = &'a T;
    type IntoIter = ULLIter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        ULLIter {
            node: &self.head,
            index: 0,
        }
    }
}

pub(crate) struct ULLIter<'a, T, const N: usize> {
    node: &'a ULLNode<T, N>,
    index: usize,
}

impl<'a, T, const N: usize> Iterator for ULLIter<'a, T, N> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index > 0 && self.index.is_multiple_of(N) {
            let next_ptr = self.node.next.load(SeqCst);
            if next_ptr.is_null() {
                return None;
            }
            self.node = unsafe { &*next_ptr };
        }
        let item = &self.node.items[self.index % N];
        self.index += 1;
        Some(item)
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::{ULLNode, ULL};
    use std::array::from_fn;
    use std::sync::atomic::AtomicBool;
    use std::sync::atomic::Ordering::{Relaxed, SeqCst};
    use std::thread;

    #[test]
    fn test_concurrent_mutate_miri() {
        test_concurrent_mutate::<2, 5, 5>();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_concurrent_mutate_no_miri() {
        test_concurrent_mutate::<3, 24, 3>();
    }

    fn test_concurrent_mutate<const N: usize, const T: usize, const I: usize>() {
        let ull: ULL<AtomicBool, N> = ULL {
            head: ULLNode {
                items: from_fn(|_| AtomicBool::default()),
                next: Default::default(),
            },
        };

        fn try_claim_slot(slot: &AtomicBool) -> bool {
            slot.compare_exchange(false, true, SeqCst, Relaxed).is_ok()
        }

        thread::scope(|scope| {
            for _ in 0..T {
                scope.spawn(|| {
                    for _ in 0..I {
                        for slot in ull.into_iter() {
                            if try_claim_slot(slot) {
                                slot.store(false, SeqCst);
                                return;
                            }
                        }
                        let slot = ull.apply(try_claim_slot);
                        slot.store(false, SeqCst);
                    }
                });
            }
        });

        for slot in ull.into_iter() {
            assert!(!slot.load(Relaxed));
        }
    }
}
