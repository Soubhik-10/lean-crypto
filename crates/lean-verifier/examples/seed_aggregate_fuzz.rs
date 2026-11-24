//! Export checked honest and hostile inputs for the aggregate fuzz targets.

use lean_verifier::{AggregateClaims, AggregateProof, B256, BYTECODE_VARIABLES, Verifier};
use lean_vm::{AggregateClaims as ReferenceClaims, AggregateProof as ReferenceProof, OutputClaims};
use std::{fs, io::Write, path::Path};

fn claims(reference: &ReferenceClaims) -> AggregateClaims {
    AggregateClaims {
        lean_xmss: reference
            .lean_xmss
            .iter()
            .map(|(key, message)| (B256::new(key.to_bytes()), B256::new(*message)))
            .collect(),
        lean_sphincs: reference
            .lean_sphincs
            .iter()
            .map(|(key, message)| (B256::new(key.to_bytes()), B256::new(*message)))
            .collect(),
        da_commitment: reference.da_commitment.map(B256::new),
    }
}

fn input(claims: &AggregateClaims, proof: &[u8]) -> Vec<u8> {
    let mut encoded = vec![
        1,
        u8::try_from(claims.lean_xmss.len()).unwrap(),
        u8::try_from(claims.lean_sphincs.len()).unwrap(),
        u8::from(claims.da_commitment.is_some()),
    ];
    for list in [&claims.lean_xmss, &claims.lean_sphincs] {
        for (key, message) in list {
            encoded.extend(key.as_slice());
            encoded.extend(message.as_slice());
        }
    }
    if let Some(root) = claims.da_commitment {
        encoded.extend(root.as_slice());
    }
    encoded.extend(proof);
    encoded
}

fn write_case(
    output: &Path,
    name: &str,
    claims: &AggregateClaims,
    bytes: &[u8],
    verifier: &Verifier,
    valid: bool,
) {
    let verdict = AggregateProof::from_bytes(bytes)
        .is_ok_and(|proof| verifier.verify(claims, &proof).is_ok());
    assert_eq!(verdict, valid, "seed verdict: {name}");
    fs::write(output.join("aggregate_decode").join(name), bytes).unwrap();
    fs::write(
        output.join("aggregate_verify").join(name),
        input(claims, bytes),
    )
    .unwrap();
}

fn signature(
    seed: u8,
    message: u8,
) -> (
    lean_vm::lean_sphincs::LeanSphincsPublicKey,
    [u8; 32],
    lean_vm::lean_sphincs::LeanSphincsSignature,
) {
    let seed = B256::repeat_byte(seed);
    let message = B256::repeat_byte(message);
    let key = lean_sphincs::key_gen(&seed);
    let signature = lean_sphincs::sign(&seed, &message).unwrap();
    (
        lean_vm::lean_sphincs::LeanSphincsPublicKey::from_bytes(&key.0),
        message.0,
        lean_vm::lean_sphincs::LeanSphincsSignature::from_bytes(&signature.0),
    )
}

fn export_proof(
    output: &Path,
    name: &str,
    claims: &ReferenceClaims,
    proof: &ReferenceProof,
    verifier: &Verifier,
) {
    write_case(
        output,
        name,
        &self::claims(claims),
        &proof.to_bytes(),
        verifier,
        true,
    );
}

fn main() {
    let mut output = std::path::PathBuf::from("fuzz/corpus");
    let mut threads = 4;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => output = args.next().expect("--out requires a path").into(),
            "--threads" => {
                threads = args
                    .next()
                    .expect("--threads requires a count")
                    .parse()
                    .expect("thread count");
                assert!((1..=256).contains(&threads), "threads must be in 1..=256");
            }
            "--help" | "-h" => {
                println!("Usage: bash scripts/seed_aggregate_fuzz.sh [--out PATH] [--threads N]");
                return;
            }
            _ => panic!("unknown option: {arg}"),
        }
    }
    fs::create_dir_all(output.join("aggregate_decode")).unwrap();
    fs::create_dir_all(output.join("aggregate_verify")).unwrap();
    lean_vm::setup(threads);
    let program = reference_aggregation::unified_guest().stacked_bytecode();
    let verifier = Verifier::new(program).unwrap();
    let mut file =
        std::io::BufWriter::new(fs::File::create(output.join("aggregate-program.bin")).unwrap());
    for word in program {
        file.write_all(&word.to_le_bytes()).unwrap();
    }
    file.flush().unwrap();

    let mut children = Vec::new();
    for rate in 1..=4 {
        let (claims, proof) = lean_vm::aggregate(
            &[],
            vec![],
            vec![signature(81, rate as u8)],
            None,
            OutputClaims::All,
            rate,
        )
        .unwrap();
        export_proof(
            &output,
            &format!("leaf-rate-{rate}"),
            &claims,
            &proof,
            &verifier,
        );
        if rate <= 2 {
            children.push((claims, proof));
        }
    }
    let (expected, recursive) =
        lean_vm::aggregate(&children, vec![], vec![], None, OutputClaims::All, 1).unwrap();
    let expected = claims(&expected);
    let bytes = recursive.to_bytes();
    write_case(&output, "recursive", &expected, &bytes, &verifier, true);
    let mut changed = bytes.clone();
    changed[8] ^= 1;
    write_case(
        &output,
        "wrong-deferred-point",
        &expected,
        &changed,
        &verifier,
        false,
    );
    let mut changed = bytes.clone();
    let header = 8 + BYTECODE_VARIABLES * 16 + 4;
    changed[header + 8] = 1;
    write_case(
        &output,
        "high-limb-header",
        &expected,
        &changed,
        &verifier,
        false,
    );
    let mut changed_claims = expected.clone();
    changed_claims.lean_sphincs.reverse();
    write_case(
        &output,
        "unsorted-claims",
        &changed_claims,
        &bytes,
        &verifier,
        false,
    );
    let mut changed_claims = expected.clone();
    changed_claims
        .lean_sphincs
        .push(changed_claims.lean_sphincs[0]);
    changed_claims.lean_sphincs.sort_unstable();
    write_case(
        &output,
        "duplicate-claims",
        &changed_claims,
        &bytes,
        &verifier,
        false,
    );
    let mut changed_claims = expected.clone();
    changed_claims.lean_sphincs[0].1[0] ^= 1;
    changed_claims.lean_sphincs.sort_unstable();
    write_case(
        &output,
        "wrong-message",
        &changed_claims,
        &bytes,
        &verifier,
        false,
    );

    let mut empty = vec![0; 8 + BYTECODE_VARIABLES * 16 + 8];
    empty[..8].copy_from_slice(&(BYTECODE_VARIABLES as u64).to_le_bytes());
    empty[8] = 1;
    write_case(
        &output,
        "empty-execution",
        &expected,
        &empty,
        &verifier,
        false,
    );

    let (secret, key) = lean_vm::lean_xmss::key_gen(&[82; 32]);
    secret.prepare(7);
    let message = [83; 32];
    let sig = lean_vm::lean_xmss::sign(&secret, &message, 7);
    let blob: lean_vm::lean_da::Blob = core::array::from_fn(|i| (i as u128).wrapping_mul(13));
    let matrix = lean_vm::lean_da::BlobMatrix::build(&[blob]).unwrap();
    let (expected, proof) = lean_vm::aggregate(
        &[],
        vec![(key, message, sig)],
        vec![signature(84, 85)],
        Some(&matrix),
        OutputClaims::All,
        1,
    )
    .unwrap();
    export_proof(&output, "both-schemes-da", &expected, &proof, &verifier);
    let mut expected = claims(&expected);
    expected.da_commitment = None;
    write_case(
        &output,
        "missing-da",
        &expected,
        &proof.to_bytes(),
        &verifier,
        false,
    );
    println!(
        "Exported checked aggregate seeds and pinned program to {}",
        output.display()
    );
}
