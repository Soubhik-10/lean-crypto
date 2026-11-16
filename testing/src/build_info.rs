use alloy_primitives::Keccak256;
include!(concat!(env!("OUT_DIR"), "/built_sources.rs"));

pub fn build_metadata() -> serde_json::Value {
    let mut hash = Keccak256::new();
    for (path, bytes) in SOURCE_FILES {
        hash.update((path.len() as u64).to_le_bytes());
        hash.update(path.as_bytes());
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    serde_json::json!({
        "rustc": env!("DIFF_RUSTC"), "llvm": env!("DIFF_LLVM"),
        "encoded_rustflags": env!("DIFF_RUSTFLAGS"),
        "compiled_source_keccak256": format!("{:#x}", hash.finalize()),
        "source_files": SOURCE_FILES.iter().map(|(path, _)| *path).collect::<Vec<_>>(),
        "backend": crate::backend(), "reference_revision": crate::REFERENCE_REVISION,
    })
}
