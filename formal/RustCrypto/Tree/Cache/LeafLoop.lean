module
public import RustCrypto.Tree.Cache.Leaf
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem leaf_loop_spec (address : Address) (nodes : Nodes) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (index : Usize) (hindex : index.val ≤ 1024)
    (hframe : TreePrimitives.frame address seed .top 0)
    (hvalues : ∀ j < index.val, nativeNode (nodes[1024+j]!) = value seed secret 0 j) :
    lean_sphincs.tree.TopTree.new_loop0 address secret nodes index ⦃ out =>
      TreePrimitives.frame out.1 seed .top 0 ∧ levelValid out.2 seed secret 0 ⦄ := by
  unfold lean_sphincs.tree.TopTree.new_loop0
  apply loop.spec_decr_nat
    (fun state : Address × Nodes × Usize => 1024-state.2.2.val)
    (fun state => state.2.2.val ≤ 1024 ∧ TreePrimitives.frame state.1 seed .top 0 ∧
      ∀ j < state.2.2.val, nativeNode (state.2.1[1024+j]!) = value seed secret 0 j)
  · rintro ⟨currentAddress,currentNodes,currentIndex⟩ ⟨hbound,hcurrentFrame,hcurrentValues⟩
    dsimp only at hbound hcurrentFrame hcurrentValues
    dsimp only
    by_cases hrun : currentIndex.val < 1024
    · apply WP.spec_mono (leaf_body_spec currentAddress currentNodes seed secret currentIndex hrun hcurrentFrame)
      intro result hresult
      cases result with
      | done v => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextNodes,nextIndex⟩
        rcases hresult with ⟨hnext,hnextFrame,leaf,slot,hslot,hnodes,hleaf⟩
        dsimp only
        refine ⟨⟨by omega,hnextFrame,?_⟩,by omega⟩
        intro j hj
        rw [hnodes,array_set_read currentNodes slot leaf (1024+j) (show 1024+j < 2048 by omega)]
        by_cases heq : j = currentIndex.val
        · have hs : 1024+j = slot.val := by omega
          rw [ite_eq_left hs]
          simpa only [heq] using hleaf
        · have hs : 1024+j ≠ slot.val := by omega
          simp only [ite_eq_right hs]
          exact hcurrentValues j (by omega)
    · have hc : currentIndex.val = 1024 := by omega
      unfold lean_sphincs.tree.TopTree.new_loop0.body
      step with top_leaves_spec as ⟨limit,hlimit⟩
      rw [hlimit]
      have hstop : ¬currentIndex < 1024#usize := by scalar_tac
      simp only [ite_eq_right hstop,WP.spec_ok]
      refine ⟨hcurrentFrame,?_⟩
      intro j hj
      exact hcurrentValues j (by simpa only [hc,width_zero] using hj)
  · exact ⟨hindex,hframe,hvalues⟩

@[step] theorem all_leaves_spec (address : Address) (nodes : Nodes) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (hframe : TreePrimitives.frame address seed .top 0) :
    lean_sphincs.tree.TopTree.new_loop0 address secret nodes 0#usize ⦃ out =>
      TreePrimitives.frame out.1 seed .top 0 ∧ levelValid out.2 seed secret 0 ⦄ := by
  apply leaf_loop_spec address nodes seed secret 0#usize (by scalar_tac) hframe
  intro j hj
  scalar_tac

end RustCrypto.TopCache
