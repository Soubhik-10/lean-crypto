module
public import RustCrypto.WotsAvx2TailBody
public import RustCrypto.WotsAvx2QueueFacts
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem tail_loop_spec (original nodes : Aeneas.Std.Array Node 16#usize) (address : Address)
    (offset : Usize) (step : U8) (chains : Aeneas.Std.Array Usize 4#usize) (count tail : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (htail : tail.val ≤ count.val) (hcount : count.val ≤ 4) (hoffset : offset.val+16 ≤ 64)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) (hdistinct : queueDistinct chains count.val)
    (hframe : keyFrame address seed key .wotsHash)
    (hvalues : ∀ j < 16, nativeNode (nodes[j]!) =
      if queued chains tail.val j then chainHash seed key (offset.val+j) step.val (nativeNode (original[j]!))
      else nativeNode (original[j]!)) :
    lean_sphincs.wots.recover_window_loop0_loop1 address offset nodes step chains count tail ⦃ out =>
      keyFrame out.1 seed key .wotsHash ∧
      ∀ j < 16, nativeNode (out.2[j]!) =
        if queued chains count.val j then chainHash seed key (offset.val+j) step.val (nativeNode (original[j]!))
        else nativeNode (original[j]!) ⦄ := by
  classical
  unfold lean_sphincs.wots.recover_window_loop0_loop1
  apply loop.spec_decr_nat
    (fun state : Address × Aeneas.Std.Array Node 16#usize × Usize => count.val-state.2.2.val)
    (fun state => state.2.2.val ≤ count.val ∧ keyFrame state.1 seed key .wotsHash ∧
      ∀ j < 16, nativeNode (state.2.1[j]!) =
        if queued chains state.2.2.val j then chainHash seed key (offset.val+j) step.val (nativeNode (original[j]!))
        else nativeNode (original[j]!))
  · rintro ⟨currentAddress,currentNodes,currentTail⟩ ⟨hbound,hcurrentFrame,hcurrentValues⟩
    dsimp only at hbound hcurrentFrame hcurrentValues
    dsimp only
    by_cases hrun : currentTail.val < count.val
    · apply WP.spec_mono (tail_body_spec currentAddress currentNodes offset step chains count currentTail seed key
        hrun hcount hoffset hchains hcurrentFrame)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextNodes,nextTail⟩
        rcases hresult with ⟨hnext,hnextFrame,root,hnodes,hroot⟩
        dsimp only
        refine ⟨⟨by omega,hnextFrame,?_⟩,by omega⟩
        have hselected : (chains[currentTail.val]!).val < 16 := hchains currentTail.val (by omega)
        have hfuture := not_queued_future chains count.val currentTail.val currentTail.val (by omega) hrun hdistinct
        have hinput : nativeNode (currentNodes[(chains[currentTail.val]!).val]!) =
            nativeNode (original[(chains[currentTail.val]!).val]!) := by
          simpa only [ite_eq_right hfuture] using hcurrentValues (chains[currentTail.val]!).val hselected
        rw [hinput] at hroot
        intro j hj
        rw [hnodes,native_set_read _ _ _ j hj,hnext]
        have hqueued := queued_succ chains currentTail.val j (by omega)
        by_cases heq : j = (chains[currentTail.val]!).val
        · have hnew : queued chains (currentTail.val+1) j := hqueued.mpr (Or.inr heq)
          simp only [ite_eq_left heq,ite_eq_left hnew]
          simpa only [heq] using hroot
        · have hnew : queued chains (currentTail.val+1) j ↔ queued chains currentTail.val j := by
            rw [hqueued]
            exact or_iff_left heq
          simp only [ite_eq_right heq,hnew]
          exact hcurrentValues j hj
    · have heq : currentTail.val = count.val := by omega
      have hstop : ¬currentTail < count := by scalar_tac
      simp only [lean_sphincs.wots.recover_window_loop0_loop1.body,ite_eq_right hstop,WP.spec_ok]
      exact ⟨hcurrentFrame,by simpa only [heq] using hcurrentValues⟩
  · exact ⟨htail,hframe,hvalues⟩

@[step] theorem tail_zero_spec (nodes : Aeneas.Std.Array Node 16#usize) (address : Address)
    (offset : Usize) (step : U8) (chains : Aeneas.Std.Array Usize 4#usize) (count : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hcount : count.val ≤ 4) (hoffset : offset.val+16 ≤ 64)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) (hdistinct : queueDistinct chains count.val)
    (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_window_loop0_loop1 address offset nodes step chains count 0#usize ⦃ out =>
      keyFrame out.1 seed key .wotsHash ∧
      ∀ j < 16, nativeNode (out.2[j]!) =
        if queued chains count.val j then chainHash seed key (offset.val+j) step.val (nativeNode (nodes[j]!))
        else nativeNode (nodes[j]!) ⦄ := by
  apply tail_loop_spec nodes nodes address offset step chains count 0#usize seed key
    (by scalar_tac) hcount hoffset hchains hdistinct hframe
  intro j hj
  simp only [show (0#usize).val = 0 from rfl,queued_zero,ite_false]

end RustCrypto.WotsAvx2
