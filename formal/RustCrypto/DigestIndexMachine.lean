module
public import RustCrypto.DigestIndexBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.MessageHashBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem raw_tree_bound (digest : Aeneas.Std.Array U8 34#usize) : rawTree digest < 262144 := Nat.mod_lt _ (by decide)

theorem raw_leaf_bound (digest : Aeneas.Std.Array U8 34#usize) : rawLeaf digest < 256 := by
  unfold rawLeaf
  scalar_tac

theorem digest_index_bound (digest : Aeneas.Std.Array U8 34#usize) :
    EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest) < 67108864 := by
  rw [digest_index_native]
  have ht := raw_tree_bound digest
  have hl := raw_leaf_bound digest
  omega

/-- The machine-word mask discards exactly the six unused high tree-index bits. -/
theorem masked_tree_val (digest : Aeneas.Std.Array U8 34#usize) :
    ((core.num.U32.from_be_bytes (Aeneas.Std.Array.make 4#usize
      [0#u8,digest.val[30]!,digest.val[31]!,digest.val[32]!])) &&& 262143#u32).val = rawTree digest := by
  rw [UScalar.val_and,ForsDigest.field24_val]
  have hm : (262143#u32).val = 2^18-1 := rfl
  rw [hm,Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- The actual machine-word shift, join and widening build the full 26-bit index without overflow. -/
@[step] theorem merge_index_spec (tree : U32) (leaf : U8) (htree : tree.val < 262144) :
    (do
      let shifted ← tree <<< 8#i32
      let low ← lift (core.convert.num.FromU32U8.from leaf)
      let joined ← lift (shifted ||| low)
      lift (core.convert.num.FromU64U32.from joined)) ⦃ out => out.val = tree.val*256+leaf.val ⦄ := by
  step as ⟨shifted,hshifted⟩
  have hs : shifted.val = tree.val*256 := by
    norm_num [Nat.shiftLeft_eq,U32.size,U32.numBits,UScalarTy.numBits] at hshifted
    omega
  step with WotsChain.widen_step_spec leaf as ⟨low,hlow⟩
  step as ⟨joined,hjoined⟩
  have hj : joined.val = tree.val*256+leaf.val := by
    rw [hjoined,UScalar.val_or,hs,hlow,Nat.mul_comm tree.val 256]
    exact (Nat.two_pow_add_eq_or_of_lt (show leaf.val < 2^8 by scalar_tac) tree.val).symm
  simpa only [lift,WP.spec_ok,core.convert.num.FromU64U32.from_val_eq] using hj

end RustCrypto.MessageHashBridge
