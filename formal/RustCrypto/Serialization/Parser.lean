module

public import LeanSphincs.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Source-derived parser contracts, relative to Aeneas and the explicitly
supplied Rust standard-library models in RustParser.Models. -/
namespace RustParser

theorem is_empty_eq (bytes : Slice U8) :
    lean_sphincs.signature.Reader.is_empty bytes = .ok (decide (bytes.val.length = 0)) := by rfl

theorem new_eq (bytes : Slice U8) :
    lean_sphincs.signature.Reader.new bytes = .ok bytes := by rfl

theorem take_success (n : Usize) (bytes : Slice U8) (h : n.val ≤ bytes.val.length) :
    lean_sphincs.signature.Reader.take n bytes =
      .ok (some (readPrefix n bytes h), readSuffix n bytes) := by
  simp [lean_sphincs.signature.Reader.take, core.slice.Slice.split_first_chunk, h,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]

theorem take_failure (n : Usize) (bytes : Slice U8) (h : bytes.val.length < n.val) :
    lean_sphincs.signature.Reader.take n bytes = .ok (none, bytes) := by
  simp [lean_sphincs.signature.Reader.take, core.slice.Slice.split_first_chunk,
    show ¬n.val ≤ bytes.val.length by omega,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

theorem take_total (n : Usize) (bytes : Slice U8) :
    ∃ output, lean_sphincs.signature.Reader.take n bytes = .ok output := by
  by_cases h : n.val ≤ bytes.val.length
  · exact ⟨_, take_success n bytes h⟩
  · exact ⟨_, take_failure n bytes (by omega)⟩

theorem successful_read_conserves_bytes (n : Usize) (bytes : Slice U8)
    (h : n.val ≤ bytes.val.length) :
    (readPrefix n bytes h).val ++ (readSuffix n bytes).val = bytes.val := by
  simp [readPrefix, readSuffix]

theorem successful_read_length (n : Usize) (bytes : Slice U8)
    (h : n.val ≤ bytes.val.length) :
    (readPrefix n bytes h).val.length = n.val ∧
      (readSuffix n bytes).val.length = bytes.val.length - n.val := by
  simp [readPrefix, readSuffix, h]

theorem take_zero (bytes : Slice U8) :
    lean_sphincs.signature.Reader.take 0#usize bytes =
      .ok (some (Aeneas.Std.Array.empty U8), bytes) := by
  rw [take_success _ _ (by simp)]
  congr 1
  congr 1
  apply Slice.ext
  simp [readSuffix]

end RustParser
