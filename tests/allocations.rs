//! Allocation counting for the public verification API.

mod common;

use lean_sphincs::verify;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

struct CountingAllocator;

static COUNTING: AtomicBool = AtomicBool::new(false);
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

// SAFETY: All operations delegate to System with exactly the caller's arguments.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if COUNTING.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        }
        // SAFETY: The allocator contract is forwarded to System.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        // SAFETY: The allocator contract is forwarded to System.
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        if COUNTING.load(Ordering::Relaxed) {
            ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        }
        // SAFETY: The allocator contract is forwarded to System.
        unsafe { System.realloc(pointer, layout, size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

#[test]
fn verification_allocates_nothing() {
    let (public_key, message, signature) = common::known_answer();
    assert!(verify(&public_key, &message, &signature));
    COUNTING.store(true, Ordering::SeqCst);
    let valid = verify(&public_key, &message, &signature);
    COUNTING.store(false, Ordering::SeqCst);
    assert!(valid);
    assert_eq!(ALLOCATIONS.load(Ordering::SeqCst), 0);
}
