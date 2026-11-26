module
public import RustCrypto.RootBridge
public import RustCrypto.BuildSecret
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives
open RustCrypto.WotsEthlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[step] theorem build_fors_secret_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (target : U32) (path : Slice Node)
    (htarget : target.val < 1024)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.build_tree address secret
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf))
      10#u32 target path ⦃ out =>
      nativeNode out.1.2 = EthLib.Cryptography.Sphincs.forsSecret
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) idx kappa target.val ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  let model := forsModel seed secret idx kappa
  let values := EthLib.Cryptography.Sphincs.forsSecret
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa
  let kind := lean_sphincs.tree.TreeKind.Fors (stepWord kappa.val)
    (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)
  have hl : ∀ (a : Address) (i : U32), i.val < 1024 → model.frame a →
      lean_sphincs.tree.tree_leaf a secret kind i ⦃ out =>
        nativeNode out.1.2 = values i.val ∧ model.frame out.2 ⦄ := by
    intro a i hi hf
    apply WP.spec_mono (ForsPrimitives.fors_leaf_spec a seed secret idx kappa i hi hf)
    intro out hout
    exact ⟨hout.2.1,hout.2.2⟩
  have hp : ∀ (a : Address) (h i : U32) (l r : Node), h.val ≤ 10 → i.val < 2^(10-h.val) → model.frame a →
      lean_sphincs.tree.tree_parent a kind h i l r ⦃ out =>
        nativeNode out.1 = model.parent ⟨h.val,i.val⟩ (nativeNode l) (nativeNode r) ∧ model.frame out.2 ⦄ := by
    intro a h i l r hh hi hf
    exact ForsPrimitives.fors_parent_spec a seed idx kappa h i l r hh hi hf
  unfold lean_sphincs.tree.build_tree
  have hsource := build_subtree_secret_spec model values secret kind hl hp 10 address 10#u32 0#u32 target path
    rfl (by decide) (by decide) hframe
  apply WP.spec_mono hsource
  intro out hout
  constructor
  · have hchosen : selectedValue values (nativeNode zeroNode) 10 (0#u32).val target.val = values target.val := by
      unfold selectedValue
      apply ite_eq_left
      exact Nat.div_eq_of_lt htarget
    simpa only [hchosen] using hout.1
  · exact hout.2

end RustCrypto.BuildRoot
