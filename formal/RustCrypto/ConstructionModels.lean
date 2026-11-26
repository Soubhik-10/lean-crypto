module
public import RustCrypto.RootBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.TreePrimitives RustCrypto.WotsEthlib
set_option maxHeartbeats 2000000

@[step] theorem xmss_leaf_contract (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (address : Address) (index : U32) (_hindex : index.val < 1024)
    (hframe : (xmssModel seed secret layer tree).frame address) :
    lean_sphincs.tree.tree_leaf address secret .Xmss index ⦃ out =>
      nativeNode out.1.1 = (xmssModel seed secret layer tree).leaf index.val ∧ (xmssModel seed secret layer tree).frame out.2 ⦄ := by
  apply WP.spec_mono (xmss_leaf_spec address seed secret layer tree index hframe)
  intro out hout
  exact ⟨hout.1,hout.2.2⟩

@[step] theorem xmss_parent_contract (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (address : Address) (height index : U32) (left right : Node)
    (_hheight : height.val ≤ 10) (_hindex : index.val < 2^(10-height.val))
    (hframe : (xmssModel seed secret layer tree).frame address) :
    lean_sphincs.tree.tree_parent address .Xmss height index left right ⦃ out =>
      nativeNode out.1 = (xmssModel seed secret layer tree).parent ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
      (xmssModel seed secret layer tree).frame out.2 ⦄ := by
  exact xmss_parent_spec address seed layer tree height index left right hframe

@[step] theorem fors_leaf_contract (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES)
    (address : Address) (index : U32) (hindex : index.val < 1024)
    (hframe : (forsModel seed secret idx kappa).frame address) :
    lean_sphincs.tree.tree_leaf address secret (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)) index ⦃ out =>
      nativeNode out.1.1 = (forsModel seed secret idx kappa).leaf index.val ∧ (forsModel seed secret idx kappa).frame out.2 ⦄ := by
  apply WP.spec_mono (ForsPrimitives.fors_leaf_spec address seed secret idx kappa index hindex hframe)
  intro out hout
  exact ⟨hout.1,hout.2.2⟩

@[step] theorem fors_parent_contract (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES)
    (address : Address) (height index : U32) (left right : Node)
    (hheight : height.val ≤ 10) (hindex : index.val < 2^(10-height.val))
    (hframe : (forsModel seed secret idx kappa).frame address) :
    lean_sphincs.tree.tree_parent address (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)) height index left right ⦃ out =>
      nativeNode out.1 = (forsModel seed secret idx kappa).parent ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
      (forsModel seed secret idx kappa).frame out.2 ⦄ := by
  exact ForsPrimitives.fors_parent_spec address seed idx kappa height index left right hheight hindex hframe

end RustCrypto.BuildRoot
