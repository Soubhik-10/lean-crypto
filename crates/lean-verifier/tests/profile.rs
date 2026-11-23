//! Pin the fixed aggregation program against the executable reference.

use lean_verifier::{BYTECODE_VARIABLES, PROGRAM_IV, PROGRAM_WORDS, Verifier, VerifyError};

#[test]
fn profile_matches_reference() {
    let guest = reference_aggregation::unified_guest();
    assert_eq!(guest.stacked_bytecode().len(), PROGRAM_WORDS);
    assert_eq!(guest.bytecode().fiat_shamir_iv(), PROGRAM_IV);
    assert_eq!(
        guest.stacked_bytecode().len().ilog2() as usize,
        BYTECODE_VARIABLES
    );
    assert_eq!(guest.stacked_bytecode()[0], 0);
    Verifier::new(guest.stacked_bytecode()).unwrap();
}

#[test]
fn other_well_formed_programs_are_rejected() {
    let mut program = reference_aggregation::unified_guest()
        .stacked_bytecode()
        .to_vec();
    assert!(matches!(Verifier::new(&[]), Err(VerifyError::Program)));
    assert!(matches!(
        Verifier::new(&program[..PROGRAM_WORDS - 1]),
        Err(VerifyError::Program)
    ));
    // An operand change keeps a valid ISA encoding, but changes the trusted program.
    let instructions = PROGRAM_WORDS / 16;
    program[4 * instructions] ^= 1;
    let different = reference_verifier::Bytecode::new(&program).unwrap();
    assert_ne!(different.fiat_shamir_iv(), PROGRAM_IV);
    assert!(matches!(Verifier::new(&program), Err(VerifyError::Program)));
}
