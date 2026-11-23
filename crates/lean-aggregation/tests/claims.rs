//! Public claim-set behavior shared by std and no_std configurations.

use lean_aggregation::{B256, Claims};

#[test]
fn claims_use_reference_order_and_set_semantics() {
    let a = (B256::repeat_byte(1), B256::repeat_byte(9));
    let b = (B256::repeat_byte(2), B256::repeat_byte(0));
    let c = (a.0, B256::repeat_byte(8));
    let claims = Claims::new([b, a, c, b]);
    assert_eq!(claims.len(), 3);
    assert!(!claims.is_empty());
    assert_eq!(claims.iter().collect::<Vec<_>>(), [c, a, b]);
    assert_eq!(claims, Claims::new([a, b, c]));
}

#[test]
fn ordering_matches_alloy_pairs_across_key_and_message_bytes() {
    let mut pairs = Vec::new();
    for offset in [0, 15, 16, 31] {
        let mut key = B256::ZERO;
        key[offset] = 1;
        for message_offset in [0, 15, 16, 31] {
            let mut message = B256::ZERO;
            message[message_offset] = 1;
            pairs.push((key, message));
        }
    }
    pairs.reverse();
    pairs.extend_from_within(..);
    let claims = Claims::new(pairs.iter().copied());
    pairs.sort_unstable();
    pairs.dedup();
    assert_eq!(claims.iter().collect::<Vec<_>>(), pairs);
    assert_eq!(claims.len(), pairs.len());
}

#[test]
fn empty_claims_have_an_empty_iterator() {
    for claims in [Claims::default(), Claims::new([])] {
        assert!(claims.is_empty());
        assert_eq!(claims.len(), 0);
        assert_eq!(claims.iter().len(), 0);
        assert_eq!(claims.iter().next(), None);
    }
}
