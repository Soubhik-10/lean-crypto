module
public import RustCrypto.Tree.Cache.Model
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem leaf_body_spec (address : Address) (nodes : Nodes) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (index : Usize) (hindex : index.val < 1024)
    (hframe : TreePrimitives.frame address seed .top 0) :
    lean_sphincs.tree.TopTree.new_loop0.body secret address nodes index ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextNodes,nextIndex) => nextIndex.val = index.val+1 ∧
          TreePrimitives.frame nextAddress seed .top 0 ∧
          ∃ (leaf : Node) (slot : Usize), slot.val = 1024+index.val ∧ nextNodes = nodes.set slot leaf ∧
            nativeNode leaf = value seed secret 0 index.val ⦄ := by
  unfold lean_sphincs.tree.TopTree.new_loop0.body
  step with top_leaves_spec as ⟨limit,hlimit⟩
  rw [hlimit]
  have hrun : index < 1024#usize := by scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨leafIndex,hleafIndex⟩
  have hi : leafIndex.val = index.val := by scalar_tac
  step with TreePrimitives.public_leaf_index_spec address seed secret .top 0 leafIndex hframe
    as ⟨leaf,nextAddress,hleaf,hnextFrame⟩
  step as ⟨slot,hslot⟩
  step as ⟨nextNodes,hnextNodes⟩
  step as ⟨nextIndex,hnextIndex⟩
  refine ⟨hnextIndex,hnextFrame,leaf,slot,?_,hnextNodes,?_⟩
  · scalar_tac
  · rw [value_zero]
    simpa only [hi] using hleaf

end RustCrypto.TopCache
