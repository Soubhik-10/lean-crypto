module
import all LeanSphincs.Funs
public import RustCrypto.Tree.Build.Finish
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

structure Model where
  leaf : Nat → EthLib.Cryptography.Sphincs.Digest
  parent : EthLib.Cryptography.Merkle.Position → EthLib.Cryptography.Sphincs.Digest →
    EthLib.Cryptography.Sphincs.Digest → Id EthLib.Cryptography.Sphincs.Digest
  frame : Address → Prop

@[step] theorem build_subtree_root_spec (model : Model)
    (secret : Aeneas.Std.Array U8 32#usize) (kind : lean_sphincs.tree.TreeKind)
    (hleaf : ∀ (address : Address) (index : U32), index.val < 1024 → model.frame address →
      lean_sphincs.tree.tree_leaf address secret kind index ⦃ out =>
        nativeNode out.1.1 = model.leaf index.val ∧ model.frame out.2 ⦄)
    (hparent : ∀ (address : Address) (height index : U32) (left right : Node),
      height.val ≤ 10 → index.val < 2^(10-height.val) → model.frame address →
      lean_sphincs.tree.tree_parent address kind height index left right ⦃ out =>
        nativeNode out.1 = model.parent ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
        model.frame out.2 ⦄)
    (n : Nat) (address : Address) (height index target : U32) (path : Slice Node)
    (hvalue : height.val = n) (hheight : n ≤ 10) (hindex : index.val < 2^(10-n))
    (hframe : model.frame address) :
    lean_sphincs.tree.build_subtree address secret kind (height,index) target path ⦃ out =>
      nativeNode out.1.1 = EthLib.Cryptography.Merkle.node.go model.parent model.leaf n index.val ∧
      model.frame out.2.1 ⦄ := by
  induction n generalizing address height index path with
  | zero =>
    have hz : height = 0#u32 := by scalar_tac
    unfold lean_sphincs.tree.build_subtree
    simp only [Aeneas.Std.uncurry]
    rw [ite_eq_left hz]
    simp only [Aeneas.Std.bind_assoc,alloy_primitives.bits.fixed.FixedBytes.ZERO]
    step with hleaf address index (by simpa using hindex) hframe as ⟨leafResult,hv,hf⟩
    rcases leafResult with ⟨⟨leaf,leafSecret⟩,next⟩
    simp only [Aeneas.Std.uncurry,Aeneas.Std.bind_assoc]
    have hchoose : (if index = target then ok leafSecret else ok (Aeneas.Std.Array.repeat 16#usize 0#u8))
        ⦃ _ => True ⦄ := by
      by_cases he : index = target <;> simp [he,WP.spec_ok]
    step with hchoose as ⟨selected⟩
    change finish next path height index target leaf selected ⦃ _ ⦄
    apply WP.spec_mono (finish_spec next path height index target leaf selected (by scalar_tac))
    intro out hout
    rw [hout.1,hout.2]
    exact ⟨hv,hf⟩
  | succ n ih =>
    have hn : height ≠ 0#u32 := by scalar_tac
    unfold lean_sphincs.tree.build_subtree
    simp only [Aeneas.Std.uncurry]
    rw [ite_eq_right hn]
    simp only [Aeneas.Std.bind_assoc]
    have hp : 2^(10-n) = 2*2^(10-(n+1)) := by
      have he : 10-n = (10-(n+1))+1 := by omega
      rw [he,Nat.pow_succ]
      omega
    have hpbound : 2^(10-(n+1)) ≤ 1024 := by
      calc
        _ ≤ 2^10 := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
        _ = 1024 := by decide
    have hib : index.val < 1024 := by omega
    step as ⟨childHeight,hchild⟩
    step as ⟨childIndex,hchildIndex⟩
    step with ih address childHeight childIndex path (by scalar_tac) (by omega) (by rw [hchildIndex,hp]; omega)
      hframe as ⟨leftResult,hleft,hleftFrame⟩
    rcases leftResult with ⟨⟨left,leftSecret⟩,afterLeft,leftPath⟩
    simp only [Aeneas.Std.uncurry,Aeneas.Std.bind_assoc]
    step as ⟨rightIndex,hrightIndex⟩
    step with ih afterLeft childHeight rightIndex leftPath (by scalar_tac) (by omega)
      (by rw [hrightIndex,hchildIndex,hp]; omega) hleftFrame as ⟨rightResult,hright,hrightFrame⟩
    rcases rightResult with ⟨⟨right,rightSecret⟩,afterRight,rightPath⟩
    step with hparent afterRight height index left right (by scalar_tac) (by simpa only [hvalue] using hindex)
      hrightFrame as ⟨parentResult,hparentValue,hparentFrame⟩
    rcases parentResult with ⟨node,finalAddress⟩
    dsimp only at hparentValue hparentFrame hleft hright
    have hroot : nativeNode node = EthLib.Cryptography.Merkle.node.go model.parent model.leaf (n+1) index.val := by
      change nativeNode node = model.parent ⟨n+1,index.val⟩
        (EthLib.Cryptography.Merkle.node.go model.parent model.leaf n (2*index.val))
        (EthLib.Cryptography.Merkle.node.go model.parent model.leaf n (2*index.val+1))
      rw [hparentValue,hleft,hright,hvalue,hrightIndex,hchildIndex]
      simp only [Nat.mul_comm]
    step as ⟨shifted,hshifted⟩
    step as ⟨parity,hparity⟩
    have hchoose : (if parity = 0#u32 then ok leftSecret else ok rightSecret) ⦃ _ => True ⦄ := by
      by_cases he : parity = 0#u32 <;> simp [he,WP.spec_ok]
    step with hchoose as ⟨selected⟩
    change finish finalAddress rightPath height index target node selected ⦃ _ ⦄
    apply WP.spec_mono (finish_spec finalAddress rightPath height index target node selected (by scalar_tac))
    intro out hout
    rw [hout.1,hout.2]
    exact ⟨hroot,hparentFrame⟩

end RustCrypto.BuildRoot
