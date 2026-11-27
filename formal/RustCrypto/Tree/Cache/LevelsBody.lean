module
public import RustCrypto.Tree.Cache.ParentLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem levels_body_spec (address : Address) (nodes : Nodes) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (limit height : Usize)
    (hheight : height.val < 10) (hlimit : limit.val = width (height.val+1))
    (hframe : TreePrimitives.frame address seed .top 0) (hvalid : validThrough nodes seed secret height.val) :
    lean_sphincs.tree.TopTree.new_loop1.body address nodes limit height ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextNodes,nextWidth,nextHeight) => nextHeight.val = height.val+1 ∧
          TreePrimitives.frame nextAddress seed .top 0 ∧ validThrough nextNodes seed secret nextHeight.val ∧
          (nextHeight.val < 10 → nextWidth.val = width (nextHeight.val+1)) ⦄ := by
  unfold lean_sphincs.tree.TopTree.new_loop1.body
  step with KeyGen.max_tree_height_spec as ⟨maxHeight,hmaxHeight⟩
  rw [hmaxHeight]
  have hrun : height < 10#usize := by scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨nextHeight,hnextHeight⟩
  have hnextWidth : limit.val = width nextHeight.val := by simpa only [hnextHeight] using hlimit
  have hlower : ∀ level < nextHeight.val, levelValid nodes seed secret level := by
    intro level hlevel
    exact hvalid level (by omega)
  step with parent_loop_spec address nodes seed secret nextHeight limit (by omega) (by omega)
    hnextWidth hframe hlower as ⟨nextAddress,nextNodes,hnextFrame,hnextValid⟩
  have hbits := System.Platform.le_numBits
  step as ⟨nextWidth,hshift⟩
  refine ⟨hnextHeight,hnextFrame,hnextValid,?_⟩
  intro hnextSmall
  have hdiv : nextWidth.val = limit.val/2 := by
    norm_num [Nat.shiftRight_eq_div_pow] at hshift
    scalar_tac
  have hs := width_succ nextHeight.val hnextSmall
  omega

end RustCrypto.TopCache
