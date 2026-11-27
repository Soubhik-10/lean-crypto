module
public import LeanSphincs.Funs
public import Batching.Constants
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Constants
set_option maxHeartbeats 1000000

@[step] theorem remainder_spec (a b : U32) (h : b.val ≠ 0) :
    Aeneas.Std.U32.rem a b ⦃ out => out.val = a.val % b.val ⦄ := by
  exact UScalar.rem_spec a h

@[step] theorem rotations_loop_spec (rotations : Aeneas.Std.Array U32 25#usize)
    (x y : Usize) (t : U32) (hx : x.val < 5) (hy : y.val < 5) (ht : t.val ≤ 24) :
    lean_sphincs.hash.batch.rotations_loop rotations x y t ⦃ out =>
      out.val.map UScalar.val = Batching.Constants.offsetWalk (24 - t.val) t.val x.val y.val
        (rotations.val.map UScalar.val) ⦄ := by
  let expected := Batching.Constants.offsetWalk (24 - t.val) t.val x.val y.val
    (rotations.val.map UScalar.val)
  unfold lean_sphincs.hash.batch.rotations_loop
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array U32 25#usize × Usize × Usize × U32 => 24 - state.2.2.2.val)
    (fun state : Aeneas.Std.Array U32 25#usize × Usize × Usize × U32 =>
      state.2.1.val < 5 ∧ state.2.2.1.val < 5 ∧ state.2.2.2.val ≤ 24 ∧
      expected = Batching.Constants.offsetWalk (24 - state.2.2.2.val) state.2.2.2.val
        state.2.1.val state.2.2.1.val (state.1.val.map UScalar.val))
  · rintro ⟨current, cx, cy, ct⟩ ⟨hcx, hcy, hct, hmodel⟩
    dsimp only at hcx hcy hct hmodel
    have hmul : (ct.val + 1) * (ct.val + 2) ≤ 25 * 26 :=
      Nat.mul_le_mul (by omega) (by omega)
    dsimp only
    unfold lean_sphincs.hash.batch.rotations_loop.body
    split
    · step*
      refine ⟨hcy, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · rw [hmodel]
        have fuel : 24 - ct.val = (24 - (ct.val + 1)) + 1 := by scalar_tac
        rw [fuel, Batching.Constants.offsetWalk]
        simp_all
      · scalar_tac
    · step*
      have done : ct.val = 24 := by scalar_tac
      simpa [done, Batching.Constants.offsetWalk] using hmodel.symm
  · exact ⟨hx, hy, ht, rfl⟩

@[step] theorem rotations_spec : lean_sphincs.hash.batch.rotations ⦃ out =>
    out.val.map UScalar.val = Batching.Constants.rotationOffsets ⦄ := by
  unfold lean_sphincs.hash.batch.rotations
  step*
  simpa [Batching.Constants.rotationOffsets] using out_post

/-- The actual Rust-generated offsets agree entry for entry with EthLib. -/
@[step] theorem rotation_table_spec : lean_sphincs.hash.batch.ROTATIONS ⦃ out =>
    out.val.map UScalar.val =
      EthLib.Cryptography.Hash.Keccak.RHO.toList.map UInt64.toNat ⦄ := by
  unfold lean_sphincs.hash.batch.ROTATIONS
  apply WP.spec_mono rotations_spec
  intro out hout
  rw [hout]
  decide

end RustCrypto.Constants
