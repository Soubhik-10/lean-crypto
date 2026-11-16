use crate::{Failure, check_verification, fixtures};
use alloy_primitives::B256;
use lean_sphincs::SIGNATURE_BYTES;

/// Raw encoding: public key (32 bytes), message (32 bytes), then signature.
/// Short headers are zero-padded so even empty inputs exercise the verifier.
pub fn check_wire(data: &[u8]) -> Result<bool, Failure> {
    let mut key = B256::ZERO;
    let mut message = B256::ZERO;
    let key_len = data.len().min(32);
    key[..key_len].copy_from_slice(&data[..key_len]);
    if data.len() > 32 {
        let message_len = (data.len() - 32).min(32);
        message[..message_len].copy_from_slice(&data[32..32 + message_len]);
    }
    check_verification(
        &key,
        &message,
        data.get(64..).unwrap_or_default(),
        None,
        "wire",
    )
}

/// First byte selects a valid fixture; each next four bytes describes an edit.
/// Unedited fixtures stay valid, keeping the deepest verification paths reachable.
pub fn check_mutated_fixture(data: &[u8]) -> Result<bool, Failure> {
    let cases = fixtures();
    let selected = usize::from(data.first().copied().unwrap_or_default()) % cases.len();
    let fixture = &cases[selected];
    let mut key = fixture.key;
    let mut message = fixture.message;
    let mut signature = fixture.signature.clone();
    for edit in data.get(1..).unwrap_or_default().chunks_exact(4).take(64) {
        let position = usize::from(u16::from_le_bytes([edit[1], edit[2]]));
        let value = edit[3];
        match edit[0] % 8 {
            0 => {
                if !signature.is_empty() {
                    let at = position % signature.len();
                    signature[at] ^= value | 1;
                }
            }
            1 => key[position % 32] ^= value | 1,
            2 => message[position % 32] ^= value | 1,
            3 => signature.truncate(position % (SIGNATURE_BYTES + 1)),
            4 => {
                if signature.len() < SIGNATURE_BYTES + 128 {
                    signature.extend(std::iter::repeat_n(value, 1 + position % 32));
                }
            }
            5 => {
                let at = [4240, 5396, 6552][position % 3];
                if let Some(counter) = signature.get_mut(at..at + 4) {
                    counter.copy_from_slice(&[edit[1], edit[2], value, value]);
                }
            }
            6 => key.0.rotate_left(16),
            _ => {
                if !signature.is_empty() {
                    let at = position % signature.len();
                    let end = (at + 16).min(signature.len());
                    signature[at..end].fill(value);
                }
            }
        }
    }
    let expected = (data.len() < 5).then_some(true);
    check_verification(&key, &message, &signature, expected, "mutated fixture")
}
