module
public import LeanSphincs.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Actual Rust machine-word behavior at every production layer height.
These are total-correctness contracts over Aeneas's integer semantics. -/
namespace RustIndex

theorem take_layer8_spec (index : U64) :
    lean_sphincs.params.take_layer index 8#u32 ⦃ result =>
      result.1.val = index.val % 256 ∧ result.2.val = index.val / 256 ⦄ := by
  unfold lean_sphincs.params.take_layer
  step*
  norm_num [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, U64.size, U64.numBits, UScalarTy.numBits] at i_post index1_post
  norm_num [i_post] at i1_post
  simp only [UScalar.val_and, i1_post] at i2_post
  have mask : index.val &&& 255 = index.val % 256 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod index.val 8
  rw [mask] at i2_post
  constructor
  · rw [leaf_post, UScalar.cast_val_eq, i2_post]
    have bound : index.val % 256 < 256 := Nat.mod_lt _ (by decide)
    norm_num [UScalarTy.numBits]
    omega
  · exact index1_post

theorem take_layer10_spec (index : U64) :
    lean_sphincs.params.take_layer index 10#u32 ⦃ result =>
      result.1.val = index.val % 1024 ∧ result.2.val = index.val / 1024 ⦄ := by
  unfold lean_sphincs.params.take_layer
  step*
  norm_num [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, U64.size, U64.numBits, UScalarTy.numBits] at i_post index1_post
  norm_num [i_post] at i1_post
  simp only [UScalar.val_and, i1_post] at i2_post
  have mask : index.val &&& 1023 = index.val % 1024 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod index.val 10
  rw [mask] at i2_post
  constructor
  · rw [leaf_post, UScalar.cast_val_eq, i2_post]
    have bound : index.val % 1024 < 1024 := Nat.mod_lt _ (by decide)
    norm_num [UScalarTy.numBits]
    omega
  · exact index1_post

theorem layer_heights_eq : lean_sphincs.params.LAYER_HEIGHTS.val =
    [8#u32, 8#u32, 10#u32] := by
  simp [lean_sphincs.params.LAYER_HEIGHTS, Aeneas.Std.Array.make]

theorem take_layer_production_spec (index : U64) (height : U32)
    (h : height ∈ lean_sphincs.params.LAYER_HEIGHTS.val) :
    lean_sphincs.params.take_layer index height ⦃ result =>
      result.1.val = index.val % (2 ^ height.val) ∧
      result.2.val = index.val / (2 ^ height.val) ⦄ := by
  rw [layer_heights_eq] at h
  have choices : height = 8#u32 ∨ height = 10#u32 := by simpa using h
  rcases choices with h | h <;> subst height
  · simpa using take_layer8_spec index
  · simpa using take_layer10_spec index

end RustIndex
