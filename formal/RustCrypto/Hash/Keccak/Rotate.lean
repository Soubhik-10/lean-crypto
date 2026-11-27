module
public import LeanSphincs.Funs
public import Init.Data.BitVec.Lemmas
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.SimdRound
attribute [local simp] wide.u64x2_.u64x2.Insts.CoreOpsBitShlU32u64x2.shl
attribute [local simp] wide.u64x2_.u64x2.Insts.CoreOpsBitShrU32u64x2.shr
attribute [local simp] wide.u64x2_.u64x2.Insts.CoreOpsBitBitOru64x2u64x2.bitor
attribute [local simp] wide.u64x4_.u64x4.Insts.CoreOpsBitShlU32u64x4.shl
attribute [local simp] wide.u64x4_.u64x4.Insts.CoreOpsBitShrU32u64x4.shr
attribute [local simp] wide.u64x4_.u64x4.Insts.CoreOpsBitBitOru64x4u64x4.bitor

/-- The actual SIMD helper rotates each lane independently for every valid angle. -/
@[step] theorem rotate_spec (angle : U32) (word) (hangle : angle.val < 64) :
    lean_sphincs.hash.batch.rotate angle word ⦃ out =>
      ∀ lane, (out lane).bv = (word lane).bv.rotateLeft angle.val ⦄ := by
  unfold lean_sphincs.hash.batch.rotate
  split
  · simp_all [WP.spec_ok, BitVec.rotateLeft_def, BitVec.ushiftRight_eq_zero]
  · simp
    step*
    simp_all [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hangle]

end RustCrypto.SimdRound
