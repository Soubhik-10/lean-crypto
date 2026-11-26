module
public import RustCrypto.ConstructionModels
public import RustCrypto.BuildPath
public import RustCrypto.MerkleBuilt
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.TreePrimitives RustCrypto.WotsEthlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[step] theorem build_tree_path_ethlib_spec (model : Model)
    (secret : Aeneas.Std.Array U8 32#usize) (kind : lean_sphincs.tree.TreeKind)
    (hleaf : ∀ (address : Address) (index : U32), index.val < 1024 → model.frame address →
      lean_sphincs.tree.tree_leaf address secret kind index ⦃ out =>
        nativeNode out.1.1 = model.leaf index.val ∧ model.frame out.2 ⦄)
    (hparent : ∀ (address : Address) (height index : U32) (left right : Node),
      height.val ≤ 10 → index.val < 2^(10-height.val) → model.frame address →
      lean_sphincs.tree.tree_parent address kind height index left right ⦃ out =>
        nativeNode out.1 = model.parent ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
        model.frame out.2 ⦄)
    (address : Address) (height target : U32) (path : Slice Node) (hheight : height.val ≤ 10)
    (htarget : target.val < 2^height.val) (hlen : path.val.length = height.val) (hframe : model.frame address) :
    lean_sphincs.tree.build_tree address secret kind height target path ⦃ out =>
      out.2.2.val.map nativeNode =
        ((EthLib.Cryptography.Merkle.build model.parent model.leaf ⟨height.val,0⟩).path height.val target.val).toList ∧
      model.frame out.2.1 ⦄ := by
  unfold lean_sphincs.tree.build_tree
  have hi : (0#u32).val < 2^(10-height.val) := by
    change 0 < 2^(10-height.val)
    exact Nat.pow_pos (by decide)
  apply WP.spec_mono (build_subtree_path_spec model secret kind hleaf hparent height.val address height 0#u32 target path
    rfl hheight hi hframe)
  intro out hout
  have hz : (0#u32).val = 0 := rfl
  constructor
  · rw [hout.1,hz,patch_full_path (canonicalPath model target.val) height.val target.val (path.val.map nativeNode)
      htarget (by simpa using hlen)]
    simpa only [canonicalPath,siblingIndex] using
      (RustCrypto.MerklePath.build_path_list model.parent model.leaf height.val 0 target.val (Nat.div_eq_of_lt htarget)).symm
  · exact hout.2

end RustCrypto.BuildRoot
