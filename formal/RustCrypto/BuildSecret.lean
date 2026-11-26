module
import all LeanSphincs.Funs
public import RustCrypto.Selection
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[step] theorem build_subtree_secret_spec (model : Model) (secretValue : Nat → EthLib.Cryptography.Sphincs.Digest)
    (secret : Aeneas.Std.Array U8 32#usize) (kind : lean_sphincs.tree.TreeKind)
    (hleaf : ∀ (address : Address) (index : U32), index.val < 1024 → model.frame address →
      lean_sphincs.tree.tree_leaf address secret kind index ⦃ out =>
        nativeNode out.1.2 = secretValue index.val ∧ model.frame out.2 ⦄)
    (hparent : ∀ (address : Address) (height index : U32) (left right : Node),
      height.val ≤ 10 → index.val < 2^(10-height.val) → model.frame address →
      lean_sphincs.tree.tree_parent address kind height index left right ⦃ out =>
        nativeNode out.1 = model.parent ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
        model.frame out.2 ⦄)
    (n : Nat) (address : Address) (height index target : U32) (path : Slice Node)
    (hvalue : height.val = n) (hheight : n ≤ 10) (hindex : index.val < 2^(10-n))
    (hframe : model.frame address) :
    lean_sphincs.tree.build_subtree address secret kind (height,index) target path ⦃ out =>
      nativeNode out.1.2 = selectedValue secretValue (nativeNode zeroNode) n index.val target.val ∧
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
    dsimp only at hv hf
    have hchoose : (if index = target then ok leafSecret else ok (Aeneas.Std.Array.repeat 16#usize 0#u8))
        ⦃ chosen => nativeNode chosen = selectedValue secretValue (nativeNode zeroNode) 0 index.val target.val ⦄ := by
      rw [selected_zero]
      by_cases he : index = target
      · have hvEq := congrArg UScalar.val he
        simp only [ite_eq_left he,WP.spec_ok,ite_eq_left hvEq]
        exact hv
      · have hvNe : index.val ≠ target.val := fun h => he (UScalar.eq_of_val_eq h)
        simp only [ite_eq_right he,WP.spec_ok,ite_eq_right hvNe]
        rfl
    step with hchoose as ⟨selected,hselected⟩
    change finish next path height index target leaf selected ⦃ _ ⦄
    apply WP.spec_mono (finish_spec next path height index target leaf selected (by scalar_tac))
    intro out hout
    rw [hout.1,hout.2]
    exact ⟨hselected,hf⟩
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
    step as ⟨shifted,hshifted⟩
    step as ⟨parity,hparity⟩
    have hchildValue : childHeight.val = n := by scalar_tac
    have hone : (1#u32).val = 1 := rfl
    have hparityValue : parity.val = target.val / 2^n % 2 := by
      rw [hparity,UScalar.val_and,hone,Nat.and_one_is_mod,hshifted,hchildValue,Nat.shiftRight_eq_div_pow]
    have hzero : (0#u32).val = 0 := rfl
    have hcond : parity = 0#u32 ↔ target.val / 2^n % 2 = 0 := by
      constructor
      · intro he
        have h := congrArg UScalar.val he
        simpa only [hparityValue,hzero] using h
      · intro he
        apply UScalar.eq_of_val_eq
        rw [hparityValue,he]
        rfl
    have hchoose : (if parity = 0#u32 then ok leftSecret else ok rightSecret)
        ⦃ chosen => nativeNode chosen = selectedValue secretValue (nativeNode zeroNode) (n+1) index.val target.val ⦄ := by
      rw [selected_succ]
      by_cases he : parity = 0#u32
      · have hv := hcond.mp he
        simp only [ite_eq_left he,WP.spec_ok,ite_eq_left hv]
        simpa only [hchildIndex,Nat.mul_comm] using hleft
      · have hv : target.val/2^n%2 ≠ 0 := fun h => he (hcond.mpr h)
        simp only [ite_eq_right he,WP.spec_ok,ite_eq_right hv]
        simpa only [hrightIndex,hchildIndex,Nat.mul_comm] using hright
    step with hchoose as ⟨selected,hselected⟩
    change finish finalAddress rightPath height index target node selected ⦃ _ ⦄
    apply WP.spec_mono (finish_spec finalAddress rightPath height index target node selected (by omega))
    intro out hout
    rw [hout.1,hout.2]
    exact ⟨hselected,hparentFrame⟩

end RustCrypto.BuildRoot
