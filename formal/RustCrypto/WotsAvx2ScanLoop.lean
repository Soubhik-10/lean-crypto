module
public import RustCrypto.WotsAvx2ScanInvariant
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem scan_loop_spec (original nodes : Aeneas.Std.Array Node 16#usize)
    (addresses : Aeneas.Std.Array Address 4#usize) (digits : WotsRecover.Digits) (offset : Usize) (step : U8)
    (chains : Aeneas.Std.Array Usize 4#usize) (count scanned : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (hoffset : offset.val+16 ≤ 64)
    (hinv : scanInvariant original nodes digits offset step chains count scanned seed key)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_window_loop0_loop0 addresses digits offset nodes step chains count scanned ⦃ out =>
      scanInvariant original out.2.1 digits offset step out.2.2.1 out.2.2.2 16#usize seed key ∧
      (∀ j < 4, keyFrame (out.1[j]!) seed key .wotsHash) ⦄ := by
  unfold lean_sphincs.wots.recover_window_loop0_loop0
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Address 4#usize × Aeneas.Std.Array Node 16#usize ×
        Aeneas.Std.Array Usize 4#usize × Usize × Usize => 16-state.2.2.2.2.val)
    (fun state => scanInvariant original state.2.1 digits offset step state.2.2.1 state.2.2.2.1 state.2.2.2.2 seed key ∧
      ∀ j < 4, keyFrame (state.1[j]!) seed key .wotsHash)
  · rintro ⟨currentAddresses,currentNodes,currentChains,currentCount,currentScanned⟩ ⟨hcurrent,hcurrentFrames⟩
    dsimp only at hcurrent hcurrentFrames
    dsimp only
    by_cases hrun : currentScanned.val < 16
    · apply WP.spec_mono (scan_body_spec currentAddresses currentNodes digits offset step currentChains currentCount
        currentScanned seed key hrun hcurrent.2.1 hoffset hcurrent.2.2.1 hcurrentFrames)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddresses,nextNodes,nextChains,nextCount,nextScanned⟩
        rcases hresult with ⟨hnext,hnextFrames,heffect⟩
        dsimp only
        refine ⟨⟨?_,hnextFrames⟩,by omega⟩
        exact scan_invariant_next original currentNodes nextNodes digits offset step currentChains nextChains
          currentCount currentScanned nextCount nextScanned seed key hrun hcurrent hnext heffect
    · have hbound := hcurrent.1
      have hvalue : currentScanned.val = 16 := by omega
      have hscanned : currentScanned = 16#usize := by
        apply UScalar.eq_of_val_eq
        exact hvalue
      have hstop : ¬currentScanned < lean_sphincs.wots.CHAINS_PER_WINDOW := by
        simp only [lean_sphincs.wots.CHAINS_PER_WINDOW]
        scalar_tac
      simp only [lean_sphincs.wots.recover_window_loop0_loop0.body,ite_eq_right hstop,WP.spec_ok]
      exact ⟨by simpa only [hscanned] using hcurrent,hcurrentFrames⟩
  · exact ⟨hinv,hframes⟩

theorem initial_scan_invariant (nodes : Aeneas.Std.Array Node 16#usize) (digits : WotsRecover.Digits)
    (offset : Usize) (step : U8) (chains : Aeneas.Std.Array Usize 4#usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) :
    scanInvariant nodes nodes digits offset step chains 0#usize 0#usize seed key := by
  refine ⟨by decide,by decide,hchains,?_,queue_distinct_zero chains,?_⟩
  · intro j hj
    exact False.elim (queued_zero chains j hj)
  · intro j hj
    unfold scanValue
    simp only [show (0#usize).val = 0 from rfl,Nat.not_lt_zero,false_and,ite_false]

end RustCrypto.WotsAvx2
