//! Export this implementation's results for comparison with the executable Lean model.

use alloy_primitives::{B256, hex};
use lean_sphincs::{SIGNATURE_BYTES, key_gen, sign, verify};
use serde::Deserialize;
use serde_json::json;
use std::{env, fs, path::PathBuf};

#[derive(Deserialize)]
struct KeyVector {
    name: String,
    seed: String,
}

#[derive(Deserialize)]
struct SignVector {
    name: String,
    seed: String,
    message: String,
}

#[derive(Deserialize)]
struct VerifyVector {
    name: String,
    public_key: String,
    message: String,
    signature: String,
}

struct Corpus {
    root: PathBuf,
    cases: Vec<serde_json::Value>,
}

impl Corpus {
    fn add(&mut self, kind: &str, name: &str, fields: &[(&str, String)], output: Option<String>) {
        assert!(
            name.bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
        );
        let directory = self
            .root
            .join("lean_sphincs/tests/lean_sphincs/ethlib")
            .join(kind)
            .join(name);
        fs::create_dir_all(&directory).unwrap();
        let mut yaml = String::new();
        for (key, value) in fields {
            yaml.push_str(&format!("{key}: '{value}'\n"));
        }
        match output {
            Some(value) => yaml.push_str(&format!("output: '{value}'\n")),
            None => yaml.push_str("output: null\n"),
        }
        let path = directory.join("data.yaml");
        assert!(!path.exists(), "duplicate case: {kind}/{name}");
        fs::write(path, yaml).unwrap();
        self.cases.push(json!({"kind": kind, "name": name}));
    }

    fn keygen(&mut self, name: &str, seed: &str) {
        let output = seed
            .parse::<B256>()
            .ok()
            .map(|seed| format!("{:#x}", key_gen(&seed)));
        self.add("key_gen", name, &[("seed", seed.to_owned())], output);
    }

    fn signing(&mut self, name: &str, seed: &str, message: &str) {
        let output = seed
            .parse::<B256>()
            .ok()
            .zip(message.parse::<B256>().ok())
            .and_then(|(seed, message)| {
                sign(&seed, &message)
                    .ok()
                    .map(|signature| format!("0x{}", hex::encode(signature)))
            });
        self.add(
            "sign",
            name,
            &[("seed", seed.to_owned()), ("message", message.to_owned())],
            output,
        );
    }

    fn verification(&mut self, name: &str, key: &str, message: &str, signature: &[u8]) {
        let output = key
            .parse::<B256>()
            .ok()
            .zip(message.parse::<B256>().ok())
            .and_then(|(key, message)| {
                let accepted = verify(&key, &message, signature);
                // Lean's byte parser returns none for malformed lengths; our byte API returns false.
                if signature.len() == SIGNATURE_BYTES {
                    Some(accepted.to_string())
                } else {
                    assert!(!accepted, "Rust accepted malformed signature: {name}");
                    None
                }
            });
        self.add(
            "verify",
            name,
            &[
                ("public_key", key.to_owned()),
                ("message", message.to_owned()),
                ("signature", format!("0x{}", hex::encode(signature))),
            ],
            output,
        );
    }
}

fn random_bytes(state: &mut u64) -> B256 {
    let mut bytes = [0; 32];
    for byte in &mut bytes {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *byte = *state as u8;
    }
    B256::new(bytes)
}

/// This runs explicitly in the formal CI job, then Lean checks every exported result.
#[test]
#[ignore = "requires FORMAL_CASES_DIR; run through the formal conformance workflow"]
fn export_lean_conformance_cases() {
    let root = PathBuf::from(env::var_os("FORMAL_CASES_DIR").expect("set FORMAL_CASES_DIR"));
    fs::create_dir_all(&root).unwrap();
    assert!(
        fs::read_dir(&root).unwrap().next().is_none(),
        "output directory must be empty"
    );
    let generated: usize = env::var("FORMAL_CASES")
        .unwrap_or_else(|_| "2".into())
        .parse()
        .unwrap();
    assert!(
        (1..=16).contains(&generated),
        "FORMAL_CASES must be in 1..=16"
    );
    let seed = env::var("FORMAL_SEED").unwrap_or_else(|_| "31e62d70b58a940f".into());
    let mut state = u64::from_str_radix(seed.strip_prefix("0x").unwrap_or(&seed), 16).unwrap();
    assert_ne!(state, 0, "FORMAL_SEED must be nonzero");
    let initial_state = state;
    let mut corpus = Corpus {
        root,
        cases: Vec::new(),
    };

    let keys: Vec<KeyVector> = serde_json::from_str(include_str!("vectors/key_gen.json")).unwrap();
    let signatures: Vec<SignVector> =
        serde_json::from_str(include_str!("vectors/sign.json")).unwrap();
    let verifications: Vec<VerifyVector> =
        serde_json::from_str(include_str!("vectors/ethlib.json")).unwrap();
    assert_eq!(
        (keys.len(), signatures.len(), verifications.len()),
        (4, 5, 26)
    );
    for case in keys {
        corpus.keygen(&format!("pinned-{}", case.name), &case.seed);
    }
    for case in signatures {
        corpus.signing(&format!("pinned-{}", case.name), &case.seed, &case.message);
    }
    for case in verifications {
        corpus.verification(
            &format!("pinned-{}", case.name),
            &case.public_key,
            &case.message,
            &hex::decode(case.signature).unwrap(),
        );
    }

    for index in 0..generated {
        let seed = random_bytes(&mut state);
        let message = random_bytes(&mut state);
        let key = key_gen(&seed);
        let signature = sign(&seed, &message).unwrap();
        let key_hex = format!("{key:#x}");
        let message_hex = format!("{message:#x}");
        corpus.keygen(&format!("generated-{index}"), &format!("{seed:#x}"));
        corpus.signing(
            &format!("generated-{index}"),
            &format!("{seed:#x}"),
            &message_hex,
        );
        corpus.verification(
            &format!("generated-{index}-valid"),
            &key_hex,
            &message_hex,
            signature.as_slice(),
        );

        // Exercise randomizer, FORS, all layer counters, WOTS chains and authentication paths.
        let mut offsets = vec![
            0, 15, 16, 191, 4239, 4240, 4243, 4244, 5267, 5268, 5395, 5396, 5399, 5400, 6423, 6424,
            6551, 6552, 6555, 6556, 7579, 7580, 7739,
        ];
        // Every serialized node/field boundary, not only selected byte offsets.
        for boundary in (16..=4240).step_by(16) {
            offsets.extend([boundary - 1, boundary]);
        }
        for (counter, height) in [(4240, 8), (5396, 8), (6552, 10)] {
            for boundary in (counter + 4..counter + 4 + (64 + height) * 16).step_by(16) {
                offsets.extend([boundary - 1, boundary]);
            }
        }
        for _ in 0..32 {
            offsets.push(random_bytes(&mut state)[0] as usize * 31 % SIGNATURE_BYTES);
        }
        offsets.sort_unstable();
        offsets.dedup();
        for offset in offsets {
            let mut altered = signature;
            altered[offset] ^= 1;
            corpus.verification(
                &format!("generated-{index}-signature-{offset}"),
                &key_hex,
                &message_hex,
                altered.as_slice(),
            );
        }
        for offset in [0, 15, 16, 31] {
            let mut altered_key = key;
            altered_key[offset] ^= 1;
            corpus.verification(
                &format!("generated-{index}-key-{offset}"),
                &format!("{altered_key:#x}"),
                &message_hex,
                signature.as_slice(),
            );
            let mut altered_message = message;
            altered_message[offset] ^= 1;
            corpus.verification(
                &format!("generated-{index}-message-{offset}"),
                &key_hex,
                &format!("{altered_message:#x}"),
                signature.as_slice(),
            );
        }
        for length in [
            0,
            1,
            15,
            16,
            175,
            176,
            4239,
            4240,
            4243,
            4244,
            5267,
            5268,
            5395,
            5396,
            5399,
            5400,
            6423,
            6424,
            6551,
            6552,
            6555,
            6556,
            7579,
            7580,
            SIGNATURE_BYTES - 1,
        ] {
            corpus.verification(
                &format!("generated-{index}-truncated-{length}"),
                &key_hex,
                &message_hex,
                &signature[..length],
            );
        }
        let mut trailing = signature.to_vec();
        trailing.push(0);
        corpus.verification(
            &format!("generated-{index}-trailing"),
            &key_hex,
            &message_hex,
            &trailing,
        );
        corpus.verification(
            &format!("generated-{index}-zero"),
            &key_hex,
            &message_hex,
            &[0; SIGNATURE_BYTES],
        );
    }
    let manifest = json!({
        "schema_version": 1,
        "generated_cases": generated,
        "seed": format!("{initial_state:016x}"),
        "architecture": env::consts::ARCH,
        "avx2": cfg!(target_feature = "avx2"),
        "asm_keccak": cfg!(feature = "asm-keccak"),
        "cases": corpus.cases,
    });
    fs::write(
        corpus.root.join("manifest.json"),
        serde_json::to_vec_pretty(&manifest).unwrap(),
    )
    .unwrap();
    println!(
        "Exported {} cases; seed {initial_state:016x}",
        manifest["cases"].as_array().unwrap().len()
    );
}
