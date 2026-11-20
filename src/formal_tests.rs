//! Ignored component exporter, compiled only in unit-test builds. All results come from
//! the production functions in the parent crate; Lean supplies the comparison model.
extern crate std;
use self::std::{
    env, format, fs,
    path::PathBuf,
    string::{String, ToString},
    vec,
    vec::Vec,
};
use crate::{
    fors,
    hash::{HashContext, message_digest},
    signature::Reader,
    tree,
};
use alloy_primitives::{B128, B256, hex};
use serde_json::json;

struct Corpus {
    root: PathBuf,
    cases: Vec<serde_json::Value>,
}
impl Corpus {
    fn add(&mut self, kind: &str, name: &str, fields: &[(&str, String)], output: Option<String>) {
        let path = self
            .root
            .join("components")
            .join(kind)
            .join(name)
            .join("data.yaml");
        assert!(!path.exists(), "duplicate component case");
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        let mut yaml = String::new();
        for (key, value) in fields {
            yaml.push_str(&format!("{key}: '{value}'\n"));
        }
        yaml.push_str(&output.map_or_else(
            || String::from("output: null\n"),
            |v| format!("output: '{v}'\n"),
        ));
        fs::write(path, yaml).unwrap();
        self.cases.push(json!({"kind":kind,"name":name}));
    }
}
fn bytes(value: impl AsRef<[u8]>) -> String {
    format!("0x{}", hex::encode(value))
}
fn context(key: &B256, layer: u32, tree: u64) -> HashContext {
    let mut address = HashContext::new(key);
    address.set_tree(layer, tree);
    address
}

#[test]
#[ignore = "requires the formal corpus and compiled Lean component model"]
fn export_lean_components() {
    let root = PathBuf::from(env::var_os("FORMAL_CASES_DIR").expect("set FORMAL_CASES_DIR"));
    assert!(
        root.join("manifest.json").is_file(),
        "export the public API corpus first"
    );
    assert!(
        !root.join("components.json").exists(),
        "component corpus already exists"
    );
    let mut corpus = Corpus {
        root,
        cases: Vec::new(),
    };
    let key = B256::new(core::array::from_fn(|i| (i * 7 + 3) as u8));
    let seed = B256::new(core::array::from_fn(|i| (i * 37 + 11) as u8));
    let message = B128::new(core::array::from_fn(|i| (i * 13 + 5) as u8));

    // Digest indices at 8-, 16- and 26-bit boundaries are exercised independently
    // below. Real message-digest outputs also check both Keccak calls and byte order.
    for pattern in [0u8, 1, 0x7f, 0x80, 0xff] {
        let msg = B256::repeat_byte(pattern);
        let rho = [pattern; 16];
        let digest = message_digest(&key, &msg, &rho);
        corpus.add(
            "digest",
            &format!("pattern-{pattern}"),
            &[
                ("public_key", bytes(key)),
                ("message", bytes(msg)),
                ("randomizer", bytes(rho)),
            ],
            Some(bytes(digest)),
        );
    }
    for index in [
        0u32,
        1,
        254,
        255,
        256,
        257,
        65535,
        65536,
        65537,
        (1 << 26) - 2,
        (1 << 26) - 1,
    ] {
        let mut remaining = u64::from(index);
        let mut result = Vec::new();
        for height in [8, 8, 10] {
            let leaf = crate::params::take_layer(&mut remaining, height);
            result.push(format!("{leaf},{remaining}"));
        }
        corpus.add(
            "indices",
            &format!("index-{index}"),
            &[("index", index.to_string())],
            Some(result.join(";")),
        );
    }
    // Sum 127/128/129, the extreme digits, byte order and every two-bit position.
    let mut codes = vec![B128::ZERO, B128::repeat_byte(0xff), B128::repeat_byte(0xaa)];
    for position in 0..64 {
        for digit in [0u8, 1, 3] {
            let mut code = B128::repeat_byte(0xaa);
            let shift = 6 - 2 * (position % 4);
            code[position / 4] = (code[position / 4] & !(3 << shift)) | (digit << shift);
            codes.push(code);
        }
    }
    for (i, code) in codes.into_iter().enumerate() {
        corpus.add(
            "codeword",
            &format!("code-{i}"),
            &[("code", bytes(code))],
            super::codeword(&code).map(bytes),
        );
    }
    // Valid encodings chosen using the production decoder. Check scalar tails of
    // lengths 0..3 at every step in the 16-chain AVX2 window, and all digit values.
    let (layer, tree, leaf) = (0, (1u64 << 18) - 1, 255);
    let mut address = context(&key, layer, tree);
    address.set_domain(7, leaf);
    let chains: Vec<u8> = (0..1024).map(|i| (i * 29 + 17) as u8).collect();
    let mut tails = [false; 4];
    let mut digits_seen = [false; 4];
    let mut accepted = 0;
    let mut first_counter = None;
    for counter in 0u32..2000000 {
        let Some(digits) = super::codeword(&address.encode(&message, &counter.to_be_bytes()))
        else {
            continue;
        };
        first_counter.get_or_insert(counter);
        for &digit in &digits {
            digits_seen[digit as usize] = true;
        }
        for window in digits.chunks_exact(16) {
            for step in 0..3 {
                tails[window.iter().filter(|&&d| d <= step).count() % 4] = true;
            }
        }
        let mut signature = counter.to_be_bytes().to_vec();
        signature.extend_from_slice(&chains);
        let mut reader = Reader::new(&signature);
        let output =
            super::recover_wots(&mut context(&key, layer, tree), &mut reader, leaf, message);
        assert!(reader.is_empty());
        corpus.add(
            "wots",
            &format!("valid-counter-{counter}"),
            &[
                ("public_key", bytes(key)),
                ("layer", layer.to_string()),
                ("tree", tree.to_string()),
                ("leaf", leaf.to_string()),
                ("message", bytes(message)),
                ("signature", bytes(signature)),
            ],
            output.map(bytes),
        );
        accepted += 1;
        if accepted >= 8 && tails.into_iter().all(|v| v) && digits_seen.into_iter().all(|v| v) {
            break;
        }
    }
    assert!(
        tails.into_iter().all(|v| v) && digits_seen.into_iter().all(|v| v) && accepted >= 8,
        "insufficient WOTS tail coverage"
    );
    for counter in [0u32, 1, 255, 256, 65535, 65536, u32::MAX] {
        let mut signature = counter.to_be_bytes().to_vec();
        signature.extend_from_slice(&chains);
        let output = super::recover_wots(
            &mut context(&key, layer, tree),
            &mut Reader::new(&signature),
            leaf,
            message,
        );
        corpus.add(
            "wots",
            &format!("boundary-counter-{counter}"),
            &[
                ("public_key", bytes(key)),
                ("layer", layer.to_string()),
                ("tree", tree.to_string()),
                ("leaf", leaf.to_string()),
                ("message", bytes(message)),
                ("signature", bytes(signature)),
            ],
            output.map(bytes),
        );
    }
    for (layer, tree, leaf) in [
        (0, 0, 0),
        (1, 0, 0),
        (1, 1023, 255),
        (2, 0, 0),
        (2, 0, 1023),
    ] {
        let mut address = context(&key, layer, tree);
        address.set_domain(7, leaf);
        let counter = (0u32..2000000)
            .find(|c| super::codeword(&address.encode(&message, &c.to_be_bytes())).is_some())
            .expect("accepted boundary encoding");
        for counter in [counter, u32::MAX] {
            let mut signature = counter.to_be_bytes().to_vec();
            signature.extend_from_slice(&chains);
            let output = super::recover_wots(
                &mut context(&key, layer, tree),
                &mut Reader::new(&signature),
                leaf,
                message,
            );
            corpus.add(
                "wots",
                &format!("layer-{layer}-tree-{tree}-leaf-{leaf}-counter-{counter}"),
                &[
                    ("public_key", bytes(key)),
                    ("layer", layer.to_string()),
                    ("tree", tree.to_string()),
                    ("leaf", leaf.to_string()),
                    ("message", bytes(message)),
                    ("signature", bytes(signature)),
                ],
                output.map(bytes),
            );
        }
    }
    // A limit ending immediately before/after the first accepted counter checks
    // exhaustion and least-counter behavior without assuming that signing succeeds.
    let first = u64::from(first_counter.unwrap());
    for limit in [0, 1, first, first + 1, 1u64 << 32] {
        let mut output = [0; 1028];
        let result = super::sign(
            &mut context(&key, layer, tree),
            &seed,
            leaf,
            &message,
            &mut output,
            limit,
        );
        corpus.add(
            "wots_sign",
            &format!("limit-{limit}"),
            &[
                ("public_key", bytes(key)),
                ("seed", bytes(seed)),
                ("layer", layer.to_string()),
                ("tree", tree.to_string()),
                ("leaf", leaf.to_string()),
                ("message", bytes(message)),
                ("limit", limit.to_string()),
            ],
            result.map(|()| bytes(output)),
        );
    }
    for pattern in [0u8, 0xff, 0x55, 0xaa] {
        for index in [0u32, 1, 255, 256, 65535, 65536, (1 << 26) - 1] {
            let mut digest = [pattern; 34];
            let tree_index = index >> 8;
            digest[30] = (tree_index >> 16) as u8;
            digest[31] = (tree_index >> 8) as u8;
            digest[32] = tree_index as u8;
            digest[33] = index as u8;
            let opening: Vec<u8> = (0..4224)
                .map(|i| (i * 11 + pattern as usize) as u8)
                .collect();
            let mut reader = Reader::new(&opening);
            let output = fors::recover_fors(
                &mut context(&key, 0, u64::from(tree_index)),
                &mut reader,
                &digest,
                index & 255,
            );
            assert!(reader.is_empty());
            corpus.add(
                "fors",
                &format!("leaves-{pattern}-index-{index}"),
                &[
                    ("public_key", bytes(key)),
                    ("digest", bytes(digest)),
                    ("opening", bytes(opening)),
                ],
                output.map(bytes),
            );
        }
    }
    for height in [0u32, 1, 8, 10] {
        for position in [0u32, 1, 255, 256, 1023, 24575] {
            let path: Vec<u8> = (0..height as usize * 16)
                .map(|i| (i * 17 + 9) as u8)
                .collect();
            let mut address = context(&key, 2, 0);
            address.set_domain(2, 0);
            let result = tree::climb(
                &mut address,
                &mut Reader::new(&path),
                position,
                height,
                message,
            );
            corpus.add(
                "path",
                &format!("height-{height}-position-{position}"),
                &[
                    ("public_key", bytes(key)),
                    ("height", height.to_string()),
                    ("position", position.to_string()),
                    ("node", bytes(message)),
                    ("path", bytes(path)),
                ],
                result.map(bytes),
            );
        }
    }
    fs::write(corpus.root.join("components.json"),serde_json::to_vec_pretty(&json!({"schema_version":1,"cases":corpus.cases,"wots_scalar_tail_lengths":[0,1,2,3],"wots_digits":[0,1,2,3]})).unwrap()).unwrap();
    std::println!("Exported {} production component cases", corpus.cases.len());
}
