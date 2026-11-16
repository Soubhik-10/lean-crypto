use alloy_primitives::{B256, hex};
use serde::Deserialize;
use std::sync::OnceLock;

pub struct Fixture {
    pub key: B256,
    pub message: B256,
    pub signature: Vec<u8>,
}

#[derive(Deserialize)]
struct Vector {
    public_key: String,
    message: String,
    signature: String,
    expected: Option<bool>,
}

pub fn fixtures() -> &'static [Fixture] {
    static FIXTURES: OnceLock<Vec<Fixture>> = OnceLock::new();
    FIXTURES.get_or_init(|| {
        let cases: Vec<Vector> =
            serde_json::from_str(include_str!("../../tests/vectors/ethlib.json"))
                .expect("pinned fixtures");
        let cases: Vec<_> = cases
            .into_iter()
            .filter(|case| case.expected == Some(true))
            .map(|case| Fixture {
                key: case.public_key.parse().expect("fixture key"),
                message: case.message.parse().expect("fixture message"),
                signature: hex::decode(case.signature).expect("fixture signature"),
            })
            .collect();
        assert_eq!(cases.len(), 3);
        cases
    })
}
