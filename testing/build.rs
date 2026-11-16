use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

fn rust_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("source directory") {
        let path = entry.expect("source entry").path();
        if path.is_dir() {
            rust_files(&path, files);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }
}

fn main() {
    let manifest = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let root = manifest.parent().unwrap();
    let rustc = Command::new(env::var_os("RUSTC").unwrap())
        .arg("-vV")
        .output()
        .expect("rustc version");
    let rustc = String::from_utf8(rustc.stdout).unwrap();
    println!(
        "cargo:rustc-env=DIFF_RUSTC={}",
        rustc.lines().next().unwrap()
    );
    println!(
        "cargo:rustc-env=DIFF_LLVM={}",
        rustc
            .lines()
            .find(|line| line.starts_with("LLVM version:"))
            .unwrap_or("unknown")
    );
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!(
        "cargo:rustc-env=DIFF_RUSTFLAGS={}",
        env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default()
    );
    let mut files = Vec::new();
    for directory in [
        root.join("src"),
        manifest.join("src"),
        root.join("fuzz/fuzz_targets"),
    ] {
        rust_files(&directory, &mut files);
    }
    for file in [
        "Cargo.toml",
        "Cargo.lock",
        "testing/Cargo.toml",
        "testing/Cargo.lock",
        "testing/build.rs",
        "fuzz/Cargo.toml",
    ] {
        files.push(root.join(file));
    }
    files.sort();
    let mut generated = String::from("pub const SOURCE_FILES: &[(&str, &[u8])] = &[\n");
    for file in files {
        println!("cargo:rerun-if-changed={}", file.display());
        let label = file
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        generated.push_str(&format!(
            "({label:?}, include_bytes!({:?})),\n",
            file.to_string_lossy()
        ));
    }
    generated.push_str("];\n");
    fs::write(
        Path::new(&env::var_os("OUT_DIR").unwrap()).join("built_sources.rs"),
        generated,
    )
    .unwrap();
}
