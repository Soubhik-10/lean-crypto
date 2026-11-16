use alloy_primitives::{
    B256, init_keccak_cache, keccak256, keccak256_uncached, utils::KECCAK_CACHE_STATS,
};

fn assert_cache_unused(operation: &str) {
    assert_eq!(
        [
            KECCAK_CACHE_STATS.hits(),
            KECCAK_CACHE_STATS.misses(),
            KECCAK_CACHE_STATS.inserts(),
            KECCAK_CACHE_STATS.collisions(),
        ],
        [0; 4],
        "{operation} accessed Alloy's global hash cache",
    );
}

// A separate test binary isolates the process-global cache and its counters.
#[test]
fn secret_hashes_bypass_the_enabled_global_cache() {
    assert!(init_keccak_cache(64));

    // Prove that feature unification enabled the cache before testing its bypass.
    // This has the same length as the secret seed-expansion preimage.
    let probe = [0xa5; 44];
    let expected = keccak256_uncached(probe);
    assert_eq!(keccak256(probe), expected);
    assert_eq!(keccak256(probe), expected);
    assert_eq!(KECCAK_CACHE_STATS.hits(), 1);
    assert_eq!(KECCAK_CACHE_STATS.misses(), 1);
    assert_eq!(KECCAK_CACHE_STATS.inserts(), 1);
    KECCAK_CACHE_STATS.reset();

    for (seed_byte, message_byte) in [(0x42, 0x37), (0xa7, 0x5c)] {
        let seed = B256::repeat_byte(seed_byte);
        let message = B256::repeat_byte(message_byte);

        let public_key = lean_sphincs::key_gen(&seed);
        assert_cache_unused("key generation");

        let signature = lean_sphincs::sign(&seed, &message).unwrap();
        assert_cache_unused("signing");

        assert!(lean_sphincs::verify(
            &public_key,
            &message,
            signature.as_slice(),
        ));
        assert_cache_unused("verification");
    }
}
