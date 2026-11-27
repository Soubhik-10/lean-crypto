module
public import RustCrypto.Tree.Cache.LevelsBody
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem levels_loop_spec (address : Address) (nodes : Nodes) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (limit : Usize) (hlimit : limit.val = 512)
    (hframe : TreePrimitives.frame address seed .top 0) (hleaves : levelValid nodes seed secret 0) :
    lean_sphincs.tree.TopTree.new_loop1 address nodes limit 0#usize ⦃ out =>
      TreePrimitives.frame out.1 seed .top 0 ∧ validThrough out.2 seed secret 10 ⦄ := by
  unfold lean_sphincs.tree.TopTree.new_loop1
  apply loop.spec_decr_nat
    (fun state : Address × Nodes × Usize × Usize => 10-state.2.2.2.val)
    (fun state => state.2.2.2.val ≤ 10 ∧ TreePrimitives.frame state.1 seed .top 0 ∧
      validThrough state.2.1 seed secret state.2.2.2.val ∧
      (state.2.2.2.val < 10 → state.2.2.1.val = width (state.2.2.2.val+1)))
  · rintro ⟨currentAddress,currentNodes,currentWidth,currentHeight⟩ ⟨hbound,hcurrentFrame,hcurrentValid,hcurrentWidth⟩
    dsimp only at hbound hcurrentFrame hcurrentValid hcurrentWidth
    dsimp only
    by_cases hrun : currentHeight.val < 10
    · apply WP.spec_mono (levels_body_spec currentAddress currentNodes seed secret currentWidth currentHeight hrun
        (hcurrentWidth hrun) hcurrentFrame hcurrentValid)
      intro result hresult
      cases result with
      | done v => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextNodes,nextWidth,nextHeight⟩
        rcases hresult with ⟨hnext,hnextFrame,hnextValid,hnextWidth⟩
        dsimp only
        exact ⟨⟨by omega,hnextFrame,hnextValid,hnextWidth⟩,by omega⟩
    · have hc : currentHeight.val = 10 := by omega
      unfold lean_sphincs.tree.TopTree.new_loop1.body
      step with KeyGen.max_tree_height_spec as ⟨maxHeight,hmaxHeight⟩
      rw [hmaxHeight]
      have hstop : ¬currentHeight < 10#usize := by scalar_tac
      simp only [ite_eq_right hstop,WP.spec_ok]
      exact ⟨hcurrentFrame,by simpa only [hc] using hcurrentValid⟩
  · refine ⟨by scalar_tac,hframe,?_,?_⟩
    · intro level hlevel
      have heq : level = 0 := by scalar_tac
      simpa only [heq] using hleaves
    · intro h
      change limit.val = 512
      exact hlimit

end RustCrypto.TopCache
