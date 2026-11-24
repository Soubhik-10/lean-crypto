//! Invalid headers must not allocate the deferred evaluation's weight tables.

use lean_verifier::{
    AggregateClaims, AggregateProof, B256, BYTECODE_VARIABLES, Verifier, VerifyError,
};
use std::{
    alloc::{GlobalAlloc, Layout, System},
    cell::Cell,
};

struct CountingAllocator;

thread_local! {
    static ALLOCATIONS: Cell<Option<usize>> = const { Cell::new(None) };
}

fn record_allocation() {
    let _ = ALLOCATIONS.try_with(|count| {
        if let Some(value) = count.get() {
            count.set(Some(value + 1));
        }
    });
}

// SAFETY: Every allocator operation forwards the original arguments to System.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record_allocation();
        // SAFETY: Forward the caller's valid layout to the system allocator.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        // SAFETY: Forward the original allocation and layout to System.
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        record_allocation();
        // SAFETY: Forward the caller's allocation, layout and new size unchanged.
        unsafe { System.realloc(pointer, layout, size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn proof(stream: &[(u64, u64)]) -> AggregateProof {
    let mut bytes = vec![0; 8 + BYTECODE_VARIABLES * 16];
    bytes[..8].copy_from_slice(&(BYTECODE_VARIABLES as u64).to_le_bytes());
    bytes[8] = 1; // A nonzero point would allocate two evaluation weight tables.
    bytes.extend((stream.len() as u32).to_le_bytes());
    for (low, high) in stream {
        bytes.extend(low.to_le_bytes());
        bytes.extend(high.to_le_bytes());
    }
    bytes.extend(0u32.to_le_bytes());
    AggregateProof::from_bytes(&bytes).unwrap()
}

#[test]
fn hostile_headers_are_rejected_before_deferred_evaluation() {
    let verifier =
        Verifier::new(reference_aggregation::unified_guest().stacked_bytecode()).unwrap();
    let claims = AggregateClaims {
        da_commitment: Some(B256::ZERO),
        ..Default::default()
    };
    let mut cases = Vec::new();
    let mut header = [(0, 0); 8];
    header[0] = (1, 0);
    header[7] = (1, 0);
    for length in 0..=header.len() {
        cases.push(proof(&header[..length]));
    }
    for index in 0..header.len() {
        let mut changed = header;
        changed[index].1 = 1;
        cases.push(proof(&changed));
    }
    for (index, value) in [(0, u64::MAX), (1, u64::MAX), (6, u64::MAX), (7, 0), (7, 5)] {
        let mut changed = header;
        changed[index].0 = value;
        cases.push(proof(&changed));
    }
    for proof in cases {
        ALLOCATIONS.with(|count| count.set(Some(0)));
        let verdict = verifier.verify(&claims, &proof);
        let allocations = ALLOCATIONS.with(|count| count.replace(None).unwrap());
        assert_eq!(verdict, Err(VerifyError::Proof));
        assert_eq!(
            allocations, 0,
            "invalid headers must fail before deferred evaluation"
        );
    }
}
