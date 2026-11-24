//! Bounded aggregate fuzz inputs and checks of the complete public API.

pub use lean_verifier::Verifier;
use lean_verifier::{AggregateClaims, AggregateProof, B256, PROGRAM_WORDS, VerifyError};
use std::path::Path;

/// Resource policy for the fuzz harness, not a protocol limit.
pub const MAX_INPUT_BYTES: usize = 2 * 1024 * 1024;
const MAX_CLAIMS_PER_SCHEME: u8 = 32;

/// A versioned, independently supplied claim list followed by proof bytes.
///
/// Version 1: four bytes `[1, xmss_count, sphincs_count, has_da]`, then
/// `key || message` pairs for each list, an optional 32-byte DA root, and the proof.
pub struct Input<'a> {
    pub claims: AggregateClaims,
    pub proof: &'a [u8],
}

/// Decodes only the fuzz framing; the public proof decoder handles the remainder.
pub fn decode_input(data: &[u8]) -> Option<Input<'_>> {
    if data.len() > MAX_INPUT_BYTES {
        return None;
    }
    let (&[version, xmss, sphincs, da], rest) = data.split_first_chunk::<4>()?;
    if version != 1 || xmss > MAX_CLAIMS_PER_SCHEME || sphincs > MAX_CLAIMS_PER_SCHEME || da > 1 {
        return None;
    }
    let (pairs, rest) = rest.split_at_checked(64 * usize::from(xmss + sphincs))?;
    let mut claims = AggregateClaims::default();
    for (i, pair) in pairs.chunks_exact(64).enumerate() {
        let pair = (B256::from_slice(&pair[..32]), B256::from_slice(&pair[32..]));
        if i < usize::from(xmss) {
            claims.lean_xmss.push(pair);
        } else {
            claims.lean_sphincs.push(pair);
        }
    }
    let proof = if da == 1 {
        let (root, proof) = rest.split_first_chunk::<32>()?;
        claims.da_commitment = Some(B256::new(*root));
        proof
    } else {
        rest
    };
    Some(Input { claims, proof })
}

/// Checks canonical transport and a second decode without preparing a program.
pub fn check_decode(data: &[u8]) {
    if data.len() > MAX_INPUT_BYTES {
        return;
    }
    if let Ok(proof) = AggregateProof::from_bytes(data) {
        let encoded = proof.to_bytes();
        assert_eq!(encoded, data, "accepted aggregate encoding is canonical");
        assert_eq!(
            AggregateProof::from_bytes(&encoded).unwrap().to_bytes(),
            data
        );
    }
}

/// Exercises claim ordering, statement binding, deferred evaluation and VM checks.
pub fn check_verification(data: &[u8], verifier: &Verifier) {
    let Some(input) = decode_input(data) else {
        return;
    };
    let Ok(proof) = AggregateProof::from_bytes(input.proof) else {
        return;
    };
    assert_eq!(proof.to_bytes(), input.proof);
    let verdict = verifier.verify(&input.claims, &proof);
    if [&input.claims.lean_xmss, &input.claims.lean_sphincs]
        .into_iter()
        .any(|list| list.windows(2).any(|pair| pair[0] >= pair[1]))
    {
        assert_eq!(verdict, Err(VerifyError::Claims));
    }
    if verdict.is_ok() {
        // Keep the mutated lists canonical so this checks the cryptographic
        // statement binding rather than relying on an ordering rejection.
        let mut changed = input.claims.clone();
        if let Some(first) = changed.lean_sphincs.first_mut() {
            first.1[0] ^= 1;
            changed.lean_sphincs.sort_unstable();
            changed.lean_sphincs.dedup();
        } else if let Some(first) = changed.lean_xmss.first_mut() {
            first.1[0] ^= 1;
            changed.lean_xmss.sort_unstable();
            changed.lean_xmss.dedup();
        } else {
            changed.da_commitment = if changed.da_commitment.is_some() {
                None
            } else {
                Some(B256::ZERO)
            };
        }
        assert!(verifier.verify(&changed, &proof).is_err());
        let mut changed = input.claims;
        changed.da_commitment = match changed.da_commitment {
            Some(mut root) => {
                root[0] ^= 1;
                Some(root)
            }
            None => Some(B256::ZERO),
        };
        assert!(verifier.verify(&changed, &proof).is_err());
    }
}

/// Loads and validates the pinned program exported with the honest corpus.
pub fn load_verifier(path: &Path) -> Verifier {
    let bytes = std::fs::read(path).expect("run bash scripts/seed_aggregate_fuzz.sh first");
    assert_eq!(bytes.len(), PROGRAM_WORDS * 8, "unexpected program length");
    let words: Vec<_> = bytes
        .chunks_exact(8)
        .map(|word| u64::from_le_bytes(word.try_into().unwrap()))
        .collect();
    Verifier::new(&words).expect("fuzz program must match the pinned program identity")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framing_bounds_counts_flags_and_truncated_claims() {
        for header in [[0, 0, 0, 0], [1, 33, 0, 0], [1, 0, 33, 0], [1, 0, 0, 2]] {
            assert!(decode_input(&header).is_none());
        }
        for header in [[1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1]] {
            assert!(decode_input(&header).is_none());
        }
        assert!(decode_input(&[1, 0, 0]).is_none());
        assert!(decode_input(&vec![0; MAX_INPUT_BYTES + 1]).is_none());
    }

    #[test]
    fn framing_preserves_both_claim_lists_da_and_proof_bytes() {
        let mut data = vec![1, 1, 1, 1];
        for value in 1..=5 {
            data.extend([value; 32]);
        }
        data.extend([6, 7, 8]);
        let input = decode_input(&data).unwrap();
        assert_eq!(
            input.claims.lean_xmss,
            [(B256::repeat_byte(1), B256::repeat_byte(2))]
        );
        assert_eq!(
            input.claims.lean_sphincs,
            [(B256::repeat_byte(3), B256::repeat_byte(4))]
        );
        assert_eq!(input.claims.da_commitment, Some(B256::repeat_byte(5)));
        assert_eq!(input.proof, [6, 7, 8]);
    }
}
