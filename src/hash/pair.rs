//! Keccak-256 for two independent short inputs on baseline x86-64.

use super::NODE_BYTES;
use alloy_primitives::B128;
use wide::u64x2;

const STATE_LANES: usize = 25;
const RATE_LANES: usize = 17; // 136-byte rate for Keccak-256.
const ROUNDS: usize = 24;

// FIPS 202 section 3.2.5, using the same LFSR continuously across rounds.
const ROUND_CONSTANTS: [u64; ROUNDS] = {
    let mut constants = [0; ROUNDS];
    let mut lfsr = 1u8;
    let mut round = 0;
    while round < ROUNDS {
        let mut j = 0;
        while j < 7 {
            constants[round] |= ((lfsr & 1) as u64) << ((1 << j) - 1);
            let feedback = if lfsr & 0x80 != 0 { 0x71 } else { 0 };
            lfsr = (lfsr << 1) ^ feedback;
            j += 1;
        }
        round += 1;
    }
    constants
};

// FIPS 202 section 3.2.2, with lanes laid out as x + 5 * y.
const ROTATIONS: [u32; STATE_LANES] = {
    let mut rotations = [0; STATE_LANES];
    let (mut x, mut y) = (1, 0);
    let mut t = 0;
    while t < 24 {
        rotations[x + 5 * y] = (t + 1) * (t + 2) / 2 % 64;
        (x, y) = (y, (2 * x + 3 * y) % 5);
        t += 1;
    }
    rotations
};

pub(super) fn hash<const N: usize>(first: &[u8; N], second: &[u8; N]) -> [B128; 2] {
    const { assert!(N.is_multiple_of(8) && N / 8 < RATE_LANES) };

    // Each SIMD word holds the same lane from two independent sponge states.
    let mut state = [u64x2::new([0; 2]); STATE_LANES];
    for (lane, (first, second)) in state.iter_mut().zip(
        first
            .as_chunks::<8>()
            .0
            .iter()
            .zip(second.as_chunks::<8>().0),
    ) {
        *lane = u64x2::new([u64::from_le_bytes(*first), u64::from_le_bytes(*second)]);
    }
    // Whole-lane inputs fit in one block. EthLib H uses Keccak's 0x01 suffix.
    state[N / 8] = u64x2::new([0x01; 2]);
    state[RATE_LANES - 1] |= u64x2::new([1 << 63; 2]);
    permute(&mut state);

    let low = state[0].to_array();
    let high = state[1].to_array();
    core::array::from_fn(|i| {
        let mut bytes = [0; NODE_BYTES];
        bytes[..8].copy_from_slice(&low[i].to_le_bytes());
        bytes[8..].copy_from_slice(&high[i].to_le_bytes());
        B128::new(bytes)
    })
}

#[inline(always)]
fn rotate<const N: u32>(word: u64x2) -> u64x2 {
    if N == 0 {
        word
    } else {
        (word << N) | (word >> (64 - N))
    }
}

fn permute(state: &mut [u64x2; STATE_LANES]) {
    for constant in ROUND_CONSTANTS {
        let parity: [_; 5] = core::array::from_fn(|x| {
            state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
        });
        let theta: [_; 5] =
            core::array::from_fn(|x| parity[(x + 4) % 5] ^ rotate::<1>(parity[(x + 1) % 5]));
        macro_rules! lane {
            ($i:literal) => {
                rotate::<{ ROTATIONS[$i] }>(state[$i] ^ theta[$i % 5])
            };
        }
        // Rho and pi move lane (x, y) to (y, (2*x + 3*y) mod 5). List the
        // destination rows explicitly so the compiler emits immediate shifts.
        #[rustfmt::skip]
        let rotated = [
            lane!(0), lane!(6), lane!(12), lane!(18), lane!(24),
            lane!(3), lane!(9), lane!(10), lane!(16), lane!(22),
            lane!(1), lane!(7), lane!(13), lane!(19), lane!(20),
            lane!(4), lane!(5), lane!(11), lane!(17), lane!(23),
            lane!(2), lane!(8), lane!(14), lane!(15), lane!(21),
        ];
        for (row, input_row) in state
            .as_chunks_mut::<5>()
            .0
            .iter_mut()
            .zip(rotated.as_chunks::<5>().0)
        {
            for x in 0..5 {
                row[x] = input_row[x] ^ (!input_row[(x + 1) % 5] & input_row[(x + 2) % 5]);
            }
        }
        state[0] ^= u64x2::new([constant; 2]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::{NODE_INPUT_BYTES, PARENT_INPUT_BYTES};
    use alloy_primitives::keccak256_uncached;

    fn check<const N: usize>(first: &[u8; N], second: &[u8; N]) {
        let expected =
            [first, second].map(|input| B128::from_slice(&keccak256_uncached(input)[..NODE_BYTES]));
        assert_eq!(hash(first, second), expected);
    }

    #[test]
    fn paired_hashes_match_alloy() {
        for pattern in 0u8..=u8::MAX {
            let first =
                core::array::from_fn::<_, PARENT_INPUT_BYTES, _>(|i| pattern.wrapping_add(i as u8));
            let second = first.map(|byte| !byte);
            check(&first, &second);
            check(
                first.first_chunk::<NODE_INPUT_BYTES>().unwrap(),
                second.first_chunk::<NODE_INPUT_BYTES>().unwrap(),
            );
        }
    }
}
