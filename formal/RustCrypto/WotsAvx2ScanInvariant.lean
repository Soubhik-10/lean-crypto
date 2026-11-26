module
public import RustCrypto.WotsAvx2ScanBody
public import RustCrypto.WotsAvx2ScanValue
public import RustCrypto.WotsAvx2QueueFacts
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def scanInvariant (original nodes : Aeneas.Std.Array Node 16#usize) (digits : WotsRecover.Digits)
    (offset : Usize) (step : U8) (chains : Aeneas.Std.Array Usize 4#usize) (count scanned : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) : Prop :=
  scanned.val ≤ 16 ∧ count.val < 4 ∧
  (∀ j < 4, (chains[j]!).val < 16) ∧
  (∀ j, queued chains count.val j → j < scanned.val ∧ eligible digits offset step j) ∧
  queueDistinct chains count.val ∧
  ∀ j < 16, nativeNode (nodes[j]!) =
    scanValue (eligible digits offset step) (fun k => nativeNode (original[k]!))
      (fun k => chainHash seed key (offset.val+k) step.val (nativeNode (original[k]!)))
      chains count.val scanned.val j

/-- Preservation of the scan invariant, including the partial batch and distinct pending indices. -/
theorem scan_invariant_next (original nodes nextNodes : Aeneas.Std.Array Node 16#usize)
    (digits : WotsRecover.Digits) (offset : Usize) (step : U8)
    (chains nextChains : Aeneas.Std.Array Usize 4#usize) (count scanned nextCount nextScanned : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hscan : scanned.val < 16) (hinv : scanInvariant original nodes digits offset step chains count scanned seed key)
    (hnext : nextScanned.val = scanned.val+1)
    (heffect : if eligible digits offset step scanned.val then
      nextChains = chains.set count scanned ∧
      (if count.val+1 = 4 then nextCount.val = 0 ∧
        ∀ j < 16, nativeNode (nextNodes[j]!) =
          if selected4 nextChains j then chainHash seed key (offset.val+j) step.val (nativeNode (nodes[j]!))
          else nativeNode (nodes[j]!)
       else nextCount.val = count.val+1 ∧ nextNodes = nodes)
     else nextChains = chains ∧ nextCount = count ∧ nextNodes = nodes) :
    scanInvariant original nextNodes digits offset step nextChains nextCount nextScanned seed key := by
  classical
  rcases hinv with ⟨hscanned,hcount,hchains,hqueued,hdistinct,hvalues⟩
  by_cases hactive : eligible digits offset step scanned.val
  · simp only [ite_eq_left hactive] at heffect
    rcases heffect with ⟨hnextChains,heffect⟩
    rw [hnextChains]
    have hbounded := append_bounded chains count scanned hcount hscan hchains
    by_cases hflush : count.val+1 = 4
    · simp only [ite_eq_left hflush] at heffect
      rcases heffect with ⟨hzero,heffect⟩
      refine ⟨by omega,by omega,hbounded,?_,?_,?_⟩
      · intro j hj
        have : queued (chains.set count scanned) 0 j := by simpa only [hzero] using hj
        exact False.elim (queued_zero _ j this)
      · simpa only [hzero] using queue_distinct_zero (chains.set count scanned)
      · intro j hj
        rw [heffect j hj,hnextChains,hzero,hnext]
        have hselected : selected4 (chains.set count scanned) j ↔ queued chains count.val j ∨ j = scanned.val := by
          exact (queued_four (chains.set count scanned) j).symm.trans
            (by simpa only [hflush] using queued_append chains count scanned hcount j)
        by_cases hs : selected4 (chains.set count scanned) j
        · have hw := scan_value_waiting (eligible digits offset step) (fun k => nativeNode (original[k]!))
            (fun k => chainHash seed key (offset.val+k) step.val (nativeNode (original[k]!)))
            chains count.val scanned.val j (hselected.mp hs)
          rw [ite_eq_left hs,hvalues j hj,hw]
          have hf := scan_value_flush (eligible digits offset step) (fun k => nativeNode (original[k]!))
            (fun k => chainHash seed key (offset.val+k) step.val (nativeNode (original[k]!)))
            chains count scanned hcount hflush hactive hqueued j
          simpa only [ite_eq_left hs] using hf
        · rw [ite_eq_right hs,hvalues j hj]
          have hf := scan_value_flush (eligible digits offset step) (fun k => nativeNode (original[k]!))
            (fun k => chainHash seed key (offset.val+k) step.val (nativeNode (original[k]!)))
            chains count scanned hcount hflush hactive hqueued j
          simpa only [ite_eq_right hs] using hf
    · simp only [ite_eq_right hflush] at heffect
      rcases heffect with ⟨hcountNext,hnodes⟩
      refine ⟨by omega,by omega,hbounded,?_,?_,?_⟩
      · intro j hj
        have hmem : queued chains count.val j ∨ j = scanned.val := by
          apply (queued_append chains count scanned hcount j).mp
          simpa only [hcountNext] using hj
        rcases hmem with hmem|rfl
        · have hb := hqueued j hmem
          exact ⟨by omega,hb.2⟩
        · exact ⟨by omega,hactive⟩
      · have hd := queue_distinct_append chains count scanned hcount hdistinct (fun j hj => (hqueued j hj).1)
        simpa only [hcountNext] using hd
      · intro j hj
        rw [hnodes,hvalues j hj,hcountNext,hnext]
        exact (scan_value_enqueue _ _ _ chains count scanned hcount j).symm
  · simp only [ite_eq_right hactive] at heffect
    rcases heffect with ⟨hchainsEq,hcountEq,hnodesEq⟩
    rw [hchainsEq,hcountEq,hnodesEq]
    refine ⟨by omega,hcount,hchains,?_,hdistinct,?_⟩
    · intro j hj
      have hb := hqueued j hj
      exact ⟨by omega,hb.2⟩
    · intro j hj
      rw [hvalues j hj,hnext]
      exact (scan_value_skip _ _ _ chains count.val scanned.val hactive j).symm

end RustCrypto.WotsAvx2
