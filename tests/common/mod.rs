use alloy_primitives::{B256, hex};
use serde::Deserialize;

#[derive(Deserialize)]
pub(crate) struct Vector {
    pub(crate) name: String,
    pub(crate) public_key: String,
    pub(crate) message: String,
    pub(crate) signature: String,
    #[allow(
        dead_code,
        reason = "Shared with the allocation test and benchmark harness."
    )]
    pub(crate) expected: Option<bool>,
}

impl Vector {
    pub(crate) fn valid_inputs(&self) -> (B256, B256, Vec<u8>) {
        (
            self.public_key.parse().expect("fixture public key"),
            self.message.parse().expect("fixture message"),
            hex::decode(&self.signature).expect("fixture signature"),
        )
    }
}

pub(crate) fn vectors() -> Vec<Vector> {
    serde_json::from_str(include_str!("../vectors/ethlib.json")).expect("EthLib vectors")
}

pub(crate) fn known_answer() -> (B256, B256, Vec<u8>) {
    vectors()
        .into_iter()
        .find(|case| case.name == "verify_valid_known_answer")
        .expect("independent known answer")
        .valid_inputs()
}
