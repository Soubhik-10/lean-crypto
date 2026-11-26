module
public import RustCrypto.BuildRoot
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives
open RustCrypto.WotsEthlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def xmssModel (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat) : Model where
  leaf := EthLib.Cryptography.Sphincs.leaves EthLib.Cryptography.Sphincs.hashId
    (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
      (nativeNode seed) (nativeSeed secret)) layer tree
  parent := EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer tree
  frame := fun address => TreePrimitives.frame address seed layer tree

@[step] theorem xmss_subtree_root_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (height index target : U32) (path : Slice Node) (hheight : height.val ≤ 10)
    (hindex : index.val < 2^(10-height.val)) (hframe : TreePrimitives.frame address seed layer tree) :
    lean_sphincs.tree.build_subtree address secret .Xmss (height,index) target path ⦃ out =>
      nativeNode out.1.1 = EthLib.Cryptography.Sphincs.node EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) layer tree height.val index.val ∧
      TreePrimitives.frame out.2.1 seed layer tree ⦄ := by
  let model := xmssModel seed secret layer tree
  have hl : ∀ (a : Address) (i : U32), i.val < 1024 → model.frame a →
      lean_sphincs.tree.tree_leaf a secret .Xmss i ⦃ out =>
        nativeNode out.1.1 = model.leaf i.val ∧ model.frame out.2 ⦄ := by
    intro a i _ hf
    apply WP.spec_mono (xmss_leaf_spec a seed secret layer tree i hf)
    intro out hout
    exact ⟨hout.1,hout.2.2⟩
  have hp : ∀ (a : Address) (h i : U32) (l r : Node), h.val ≤ 10 → i.val < 2^(10-h.val) → model.frame a →
      lean_sphincs.tree.tree_parent a .Xmss h i l r ⦃ out =>
        nativeNode out.1 = model.parent ⟨h.val,i.val⟩ (nativeNode l) (nativeNode r) ∧ model.frame out.2 ⦄ := by
    intro a h i l r _ _ hf
    exact xmss_parent_spec a seed layer tree h i l r hf
  simpa only [model,xmssModel,EthLib.Cryptography.Sphincs.node,EthLib.Cryptography.Merkle.node] using
    build_subtree_root_spec model secret .Xmss hl hp height.val address height index target path rfl hheight hindex hframe

def forsModel (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) : Model where
  leaf := EthLib.Cryptography.Sphincs.forsLeaves EthLib.Cryptography.Sphincs.hashId
    (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
      (nativeNode seed) (nativeSeed secret)) idx kappa
  parent := EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx kappa
  frame := fun address => TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree

@[step] theorem fors_subtree_root_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES)
    (height index target : U32) (path : Slice Node) (hheight : height.val ≤ 10)
    (hindex : index.val < 2^(10-height.val))
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.build_subtree address secret
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf))
      (height,index) target path ⦃ out =>
      nativeNode out.1.1 = EthLib.Cryptography.Sphincs.forsNode EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) idx kappa height.val index.val ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  let model := forsModel seed secret idx kappa
  let kind := lean_sphincs.tree.TreeKind.Fors (stepWord kappa.val)
    (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)
  have hl : ∀ (a : Address) (i : U32), i.val < 1024 → model.frame a →
      lean_sphincs.tree.tree_leaf a secret kind i ⦃ out =>
        nativeNode out.1.1 = model.leaf i.val ∧ model.frame out.2 ⦄ := by
    intro a i hi hf
    apply WP.spec_mono (ForsPrimitives.fors_leaf_spec a seed secret idx kappa i hi hf)
    intro out hout
    exact ⟨hout.1,hout.2.2⟩
  have hp : ∀ (a : Address) (h i : U32) (l r : Node), h.val ≤ 10 → i.val < 2^(10-h.val) → model.frame a →
      lean_sphincs.tree.tree_parent a kind h i l r ⦃ out =>
        nativeNode out.1 = model.parent ⟨h.val,i.val⟩ (nativeNode l) (nativeNode r) ∧ model.frame out.2 ⦄ := by
    intro a h i l r hh hi hf
    exact ForsPrimitives.fors_parent_spec a seed idx kappa h i l r hh hi hf
  simpa only [model,forsModel,kind,EthLib.Cryptography.Sphincs.forsNode,EthLib.Cryptography.Merkle.node] using
    build_subtree_root_spec model secret kind hl hp height.val address height index target path rfl hheight hindex hframe

@[step] theorem build_fors_root_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (target : U32) (path : Slice Node)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.build_tree address secret
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf))
      10#u32 target path ⦃ out =>
      nativeNode out.1.1 = EthLib.Cryptography.Sphincs.forsRoot EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) idx kappa ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  unfold lean_sphincs.tree.build_tree
  have hh : (10#u32).val = 10 := rfl
  have hz : (0#u32).val = 0 := rfl
  simpa only [EthLib.Cryptography.Sphincs.forsRoot,EthLib.Cryptography.Merkle.root,
    EthLib.Cryptography.Merkle.node,EthLib.Cryptography.Sphincs.forsNode,
    EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT,hh,hz] using
    fors_subtree_root_ethlib_spec address seed secret idx kappa 10#u32 0#u32 target path
      (by decide) (by decide) hframe

@[step] theorem build_xmss_root_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (height target : U32) (path : Slice Node) (hheight : height.val = layer.height)
    (hframe : TreePrimitives.frame address seed layer tree) :
    lean_sphincs.tree.build_xmss address secret height target path ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.treeRoot EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) layer tree ∧
      TreePrimitives.frame out.2.1 seed layer tree ⦄ := by
  have hh : height.val ≤ 10 := by
    rw [hheight]
    cases layer <;> decide
  have hi : (0#u32).val < 2^(10-height.val) := by
    change 0 < 2^(10-height.val)
    exact Nat.pow_pos (by decide)
  unfold lean_sphincs.tree.build_xmss lean_sphincs.tree.build_tree
  step with xmss_subtree_root_ethlib_spec address seed secret layer tree height 0#u32 target path hh hi hframe
    as ⟨pair,next,remaining,hroot,hnext⟩
  rcases pair with ⟨root,selected⟩
  simp only [Aeneas.Std.uncurry,WP.spec_ok]
  constructor
  · simpa only [EthLib.Cryptography.Sphincs.treeRoot,EthLib.Cryptography.Merkle.root,
      EthLib.Cryptography.Sphincs.node,EthLib.Cryptography.Merkle.node,hheight] using hroot
  · exact hnext

end RustCrypto.BuildRoot
