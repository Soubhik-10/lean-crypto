use super::*;

fn digits(value: &Digest) -> Option<[u8; V]> {
    let mut output = [0; V];
    let mut sum = 0usize;
    for (i, byte) in value.iter().copied().enumerate() {
        for part in 0..4 {
            let digit = (byte >> (6 - 2 * part)) & 3;
            output[4 * i + part] = digit;
            sum += usize::from(digit);
        }
    }
    (sum == TARGET_SUM).then_some(output)
}

fn encoding(pk_seed: &PkSeed, key: &OtsKey, message: &Digest, counter: u32) -> Option<[u8; V]> {
    let mut input = [0; N + COUNTER_LEN];
    input[..N].copy_from_slice(message);
    input[N..].copy_from_slice(&counter.to_be_bytes());
    digits(&th(pk_seed, &key.adrs(WOTS_ENC), &input))
}

fn secrets(pk_seed: &PkSeed, seed: &B256, key: &OtsKey) -> [Digest; V] {
    let mut nodes = [[0; N]; V];
    hash_batch::<80>(
        V,
        |chain, input| {
            image(
                pk_seed,
                &key.adrs(WOTS_PRF).with_chain(chain as u32),
                &seed.0,
                input,
            );
        },
        &mut nodes,
    );
    nodes
}

fn advance(
    pk_seed: &PkSeed,
    key: &OtsKey,
    nodes: &mut [Digest; V],
    starts: &[u8; V],
    stops: &[u8; V],
) {
    for step in 0..CHAIN_LEN - 1 {
        let mut active = [0; V];
        let mut count = 0;
        for i in 0..V {
            if usize::from(starts[i]) <= step && step < usize::from(stops[i]) {
                active[count] = i;
                count += 1;
            }
        }
        let mut output = [[0; N]; V];
        hash_batch::<64>(
            count,
            |lane, input| {
                let chain = active[lane];
                image(
                    pk_seed,
                    &key.adrs(WOTS_HASH)
                        .with_chain(chain as u32)
                        .with_hash(step as u32),
                    &nodes[chain],
                    input,
                );
            },
            &mut output[..count],
        );
        for lane in 0..count {
            nodes[active[lane]] = output[lane];
        }
    }
}

pub(super) fn public_leaf(pk_seed: &PkSeed, seed: &B256, key: &OtsKey) -> Digest {
    let mut nodes = secrets(pk_seed, seed, key);
    advance(
        pk_seed,
        key,
        &mut nodes,
        &[0; V],
        &[(CHAIN_LEN - 1) as u8; V],
    );
    th_digests(pk_seed, &key.adrs(WOTS_PK), &nodes)
}

pub(super) fn sign(
    pk_seed: &PkSeed,
    seed: &B256,
    key: &OtsKey,
    message: &Digest,
) -> (u32, [Digest; V]) {
    // Search consecutive SIMD groups in order and take the first admissible
    // counter, preserving deterministic signing exactly.
    let width = hash::LANES;
    let mut counters = [[0; N]; MAX_BATCH];
    for first in (0..1u64 << 32).step_by(width) {
        let count = ((1u64 << 32) - first).min(width as u64) as usize;
        hash_batch::<68>(
            count,
            |lane, input| {
                let mut payload = [0; N + COUNTER_LEN];
                payload[..N].copy_from_slice(message);
                payload[N..].copy_from_slice(&((first + lane as u64) as u32).to_be_bytes());
                image(pk_seed, &key.adrs(WOTS_ENC), &payload, input);
            },
            &mut counters[..count],
        );
        for (lane, candidate) in counters[..count].iter().enumerate() {
            if let Some(codeword) = digits(candidate) {
                let mut nodes = secrets(pk_seed, seed, key);
                advance(pk_seed, key, &mut nodes, &[0; V], &codeword);
                return ((first + lane as u64) as u32, nodes);
            }
        }
    }
    panic!("encoding counter exhausted");
}

pub(super) fn recover(
    pk_seed: &PkSeed,
    key: &OtsKey,
    message: &Digest,
    counter: u32,
    signature: &[Digest; V],
) -> Option<Digest> {
    let starts = encoding(pk_seed, key, message, counter)?;
    let mut ends = *signature;
    advance(
        pk_seed,
        key,
        &mut ends,
        &starts,
        &[(CHAIN_LEN - 1) as u8; V],
    );
    Some(th_digests(pk_seed, &key.adrs(WOTS_PK), &ends))
}
