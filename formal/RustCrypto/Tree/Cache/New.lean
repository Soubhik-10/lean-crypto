module
public import RustCrypto.Tree.Cache.LeafLoop
public import RustCrypto.Tree.Cache.LevelsLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

/-- The complete actual top-tree constructor caches the canonical nodes at every level. -/
@[step] theorem new_ethlib_spec (address : Address) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (oldLayer : EthLib.Cryptography.Sphincs.Layer) (oldTree : Nat)
    (hframe : TreePrimitives.frame address seed oldLayer oldTree) :
    lean_sphincs.tree.TopTree.new address secret ⦃ out =>
      validThrough out.1.nodes seed secret 10 ∧ TreePrimitives.frame out.2 seed .top 0 ⦄ := by
  unfold lean_sphincs.tree.TopTree.new
  simp only [lift,bind_ok,Aeneas.Std.Array.to_slice,Slice.len]
  step as ⟨lastLayer,hlastLayer⟩
  simp [Slice.from_val,RustIndex.layer_heights_eq] at hlastLayer
  have hl : lastLayer.val = 2 := by scalar_tac
  have hcast : UScalar.cast .U32 lastLayer = stepWord EthLib.Cryptography.Sphincs.Layer.top.toNat := by
    apply UScalar.eq_of_val_eq
    change (UScalar.cast .U32 lastLayer).val = 2
    scalar_tac
  rw [hcast]
  have hzero : treeWord 0 = 0#u64 := rfl
  have htop := ContextFrame.set_tree_frame_spec address seed oldLayer .top oldTree 0 hframe
  simp only [hzero] at htop
  step with htop as ⟨topAddress,htopFrame⟩
  simp only [alloy_primitives.bits.fixed.FixedBytes.ZERO,bind_ok]
  let initial : Nodes := Aeneas.Std.Array.repeat 2048#usize (Aeneas.Std.Array.repeat 16#usize 0#u8)
  step with all_leaves_spec topAddress initial seed secret htopFrame as ⟨afterLeaves,nodes,hafterLeaves,hleaves⟩
  step with top_leaves_spec as ⟨limit,hlimit⟩
  rw [hlimit]
  step as ⟨limitWidth,hlimitWidth⟩
  have hw : limitWidth.val = 512 := by scalar_tac
  step with levels_loop_spec afterLeaves nodes seed secret limitWidth hw hafterLeaves hleaves
    as ⟨finalAddress,finalNodes,hfinalFrame,hfinalNodes⟩
  exact ⟨hfinalNodes,hfinalFrame⟩

@[step] theorem root_ethlib_spec (cache : lean_sphincs.tree.TopTree) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (hvalid : validThrough cache.nodes seed secret 10) :
    lean_sphincs.tree.TopTree.root cache ⦃ out => nativeNode out =
      EthLib.Cryptography.Sphincs.treeRoot EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) .top 0 ⦄ := by
  unfold lean_sphincs.tree.TopTree.root
  step as ⟨root,hroot⟩
  have he : root = cache.nodes[1]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos cache.nodes.val 1 (by scalar_tac)]
    exact hroot
  have hv := hvalid 10 (by omega) 0 (by simp only [width_top]; omega)
  simp only [width_top,Nat.add_zero] at hv
  rw [he]
  unfold value at hv
  simpa only [EthLib.Cryptography.Sphincs.treeRoot,EthLib.Cryptography.Sphincs.node,
    EthLib.Cryptography.Merkle.root,EthLib.Cryptography.Merkle.node,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.TOP_HEIGHT] using hv

end RustCrypto.TopCache
