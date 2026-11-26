module
public import LeanSphincs.Funs
public import RustParser
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Verifier

theorem wrong_length_rejected (public_key message : Aeneas.Std.Array U8 32#usize)
    (bytes : Slice U8) (h : bytes.val.length ≠ 7740) :
    lean_sphincs.verify public_key message bytes = .ok false := by
  have hsize : Slice.len bytes ≠ lean_sphincs.SIGNATURE_BYTES := by
    intro heq
    have := congrArg UScalar.val heq
    simp [lean_sphincs.SIGNATURE_BYTES] at this
    exact h this
  simp [lean_sphincs.verify, hsize]

theorem truncated_randomizer_rejected (public_key message : Aeneas.Std.Array U8 32#usize)
    (bytes : Slice U8) (h : bytes.val.length < 16) :
    lean_sphincs.verifier.recover_root public_key message bytes = .ok none := by
  have hf := RustParser.take_failure 16#usize bytes h
  simp [lean_sphincs.verifier.recover_root, lean_sphincs.signature.Reader.new, hf,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

theorem failed_recovery_rejected (public_key message : Aeneas.Std.Array U8 32#usize)
    (bytes : Slice U8)
    (h : lean_sphincs.verifier.recover_root public_key message bytes = .ok none) :
    lean_sphincs.verify public_key message bytes = .ok false := by
  simp [lean_sphincs.verify, h, core.option.Option.is_some_and]

end RustCrypto.Verifier
