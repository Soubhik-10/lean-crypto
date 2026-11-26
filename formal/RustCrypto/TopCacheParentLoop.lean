module
public import RustCrypto.TopCacheParentBody
public import RustCrypto.TopCacheUpdate
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem parent_loop_spec (address : Address) (nodes : Nodes) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (height limit : Usize)
    (hpos : 0 < height.val) (hheight : height.val ≤ 10) (hwidth : limit.val = width height.val)
    (hframe : TreePrimitives.frame address seed .top 0)
    (hlower : ∀ level < height.val, levelValid nodes seed secret level) :
    lean_sphincs.tree.TopTree.new_loop1_loop0 address nodes limit height 0#usize ⦃ out =>
      TreePrimitives.frame out.1 seed .top 0 ∧ validThrough out.2 seed secret height.val ⦄ := by
  have hlimit : limit.val ≤ 512 := by rw [hwidth]; exact parent_width_bound height.val hpos hheight
  unfold lean_sphincs.tree.TopTree.new_loop1_loop0
  apply loop.spec_decr_nat
    (fun state : Address × Nodes × Usize => limit.val-state.2.2.val)
    (fun state => state.2.2.val ≤ limit.val ∧ TreePrimitives.frame state.1 seed .top 0 ∧
      (∀ level < height.val, levelValid state.2.1 seed secret level) ∧
      ∀ j < state.2.2.val, nativeNode (state.2.1[width height.val+j]!) = value seed secret height.val j)
  · rintro ⟨currentAddress,currentNodes,currentIndex⟩ ⟨hbound,hcurrentFrame,hcurrentLevels,hcurrentValues⟩
    dsimp only at hbound hcurrentFrame hcurrentLevels hcurrentValues
    dsimp only
    by_cases hrun : currentIndex.val < limit.val
    · apply WP.spec_mono (parent_body_spec currentAddress currentNodes seed height limit currentIndex hheight hlimit hrun hcurrentFrame)
      intro result hresult
      cases result with
      | done v => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextNodes,nextIndex⟩
        rcases hresult with ⟨hnext,hnextFrame,root,slot,hslot,hnodes,hroot⟩
        rw [hwidth] at hslot hroot
        have hindex : currentIndex.val < width height.val := by simpa only [hwidth] using hrun
        have hcanonical : nativeNode root = value seed secret height.val currentIndex.val :=
          hroot.trans (cached_parent_value currentNodes seed secret height.val currentIndex.val hpos hheight hindex hcurrentLevels)
        dsimp only
        refine ⟨⟨by omega,hnextFrame,?_,?_⟩,by omega⟩
        · intro level hlevel
          rw [hnodes]
          exact update_preserves_lower currentNodes root seed secret height.val currentIndex.val level slot
            hpos hheight hindex hlevel hslot (hcurrentLevels level hlevel)
        · intro j hj
          have hw := width_bounded height.val
          rw [hnodes,array_set_read currentNodes slot root (width height.val+j)
            (show width height.val+j < 2048 by omega)]
          by_cases heq : j = currentIndex.val
          · have hs : width height.val+j = slot.val := by omega
            rw [ite_eq_left hs]
            simpa only [heq] using hcanonical
          · have hs : width height.val+j ≠ slot.val := by omega
            simp only [ite_eq_right hs]
            exact hcurrentValues j (by omega)
    · have hc : currentIndex.val = limit.val := by omega
      have hstop : ¬currentIndex < limit := by scalar_tac
      simp only [lean_sphincs.tree.TopTree.new_loop1_loop0.body,ite_eq_right hstop,WP.spec_ok]
      refine ⟨hcurrentFrame,?_⟩
      intro level hlevel
      by_cases heq : level = height.val
      · subst level
        intro j hj
        exact hcurrentValues j (by simpa only [hc,hwidth] using hj)
      · exact hcurrentLevels level (by omega)
  · refine ⟨by scalar_tac,hframe,hlower,?_⟩
    intro j hj
    scalar_tac

end RustCrypto.TopCache
