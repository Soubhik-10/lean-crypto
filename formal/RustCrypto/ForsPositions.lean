module
public import RustCrypto.TreePrimitives
public import EthLib.Cryptography.Sphincs.Fors
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsPositions
open RustCrypto.WotsEthlib RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TreePrimitives
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[step] theorem shift_index_spec (tree height : U32) (htree : tree.val < 24)
    (hheight : height.val ≤ 10) :
    (tree <<< height) ⦃ out => out.val = tree.val * 2^height.val ⦄ := by
  apply WP.spec_mono (U32.ShiftLeft_spec tree height (by scalar_tac))
  intro out hout
  have hp : 2^height.val ≤ 1024 := by
    exact Nat.pow_le_pow_right (by omega) hheight
  have hb : tree.val * 2^height.val < 4294967296 := by
    have hm := Nat.mul_le_mul_left tree.val hp
    omega
  have h := hout.1
  norm_num [U32.size,U32.numBits,UScalarTy.numBits,Nat.shiftLeft_eq] at h
  simpa only [Nat.mod_eq_of_lt hb] using h

theorem joined_index (shifted tree height index : U32) (hshift : shifted.val = tree.val * 2^height.val)
    (hindex : index.val < 2^height.val) :
    (shifted ||| index).val = tree.val * 2^height.val + index.val := by
  rw [UScalar.val_or,hshift,Nat.mul_comm tree.val (2^height.val)]
  exact (Nat.two_pow_add_eq_or_of_lt hindex tree.val).symm

@[step] theorem position_shift_spec (tree height index : U32) (htree : tree.val < 24)
    (hheight : height.val ≤ 10) (hindex : index.val < 2^height.val) :
    (do let shifted ← tree <<< height; lift (shifted ||| index))
      ⦃ out => out.val = tree.val * 2^height.val + index.val ⦄ := by
  step with shift_index_spec tree height htree hheight
  step
  simpa only [out_post] using joined_index shifted tree height index shifted_post hindex

end RustCrypto.ForsPositions
