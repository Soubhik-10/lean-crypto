//! Allocation counting for the public verification API.

mod common;

use lean_sphincs::{B256, key_gen, sign, verify};
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
fn signature_operations_allocate_nothing() {
    let (public_key, message, signature) = common::known_answer();
    assert!(verify(&public_key, &message, &signature));
    let seed: B256 = "0x0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186"
        .parse()
        .unwrap();
    COUNTING.store(true, Ordering::SeqCst);
    let valid = verify(&public_key, &message, &signature);
    let generated_key = key_gen(&seed);
    let generated_signature = sign(&seed, &message);
    COUNTING.store(false, Ordering::SeqCst);
    assert!(valid);
    assert_eq!(generated_key, public_key);
    assert_eq!(generated_signature.unwrap().as_slice(), signature);
    assert_eq!(ALLOCATIONS.load(Ordering::SeqCst), 0);
}
