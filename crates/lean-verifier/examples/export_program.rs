//! Export the pinned program as data for consumers that build no compiler or prover.

use lean_verifier::{PROGRAM_WORDS, Verifier};
use std::{
    env,
    fs::File,
    io::{BufWriter, Write},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args_os().skip(1);
    let output = args.next().ok_or("usage: export_program OUTPUT.bin")?;
    if args.next().is_some() {
        return Err("expected one output path".into());
    }
    let program = reference_aggregation::unified_guest();
    let words = program.stacked_bytecode();
    Verifier::new(words)?;
    let mut output = BufWriter::new(File::create_new(output)?);
    for word in words {
        output.write_all(&word.to_le_bytes())?;
    }
    output.flush()?;
    eprintln!("Exported {PROGRAM_WORDS} pinned little-endian program words.");
    Ok(())
}
