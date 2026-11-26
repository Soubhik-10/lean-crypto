module
public import RustCrypto.WotsAvx2RoundBody
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem recover_window_ethlib_spec (address : Address) (addresses : Aeneas.Std.Array Address 4#usize)
    (original : Aeneas.Std.Array Node 16#usize) (digits : WotsRecover.Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (offset : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hoffset : offset.val+16 ≤ 64) (hdigits : WotsRecover.digitRelation digits word)
    (hframe : keyFrame address seed key .wotsHash)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_window address addresses digits offset original ⦃ out =>
      keyFrame out.2.1 seed key .wotsHash ∧
      (∀ j < 4, keyFrame (out.2.2[j]!) seed key .wotsHash) ∧
      ∀ (j : Nat) (hj : j < 16), nativeNode (out.1[j]!) = WotsRecover.endValue seed key word
        ⟨offset.val+j,by change offset.val+j < 64; omega⟩ (nativeNode (original[j]!)) ⦄ := by
  classical
  unfold lean_sphincs.wots.recover_window lean_sphincs.wots.recover_window_loop0
  apply loop.spec_decr_nat
    (fun state : Address × Aeneas.Std.Array Address 4#usize × Aeneas.Std.Array Node 16#usize × U8 => 3-state.2.2.2.val)
    (fun state => state.2.2.2.val ≤ 3 ∧ keyFrame state.1 seed key .wotsHash ∧
      (∀ j < 4, keyFrame (state.2.1[j]!) seed key .wotsHash) ∧
      ∀ (j : Nat) (hj : j < 16), nativeNode (state.2.2.1[j]!) = progress seed key word
        ⟨offset.val+j,by change offset.val+j < 64; omega⟩ (nativeNode (original[j]!)) state.2.2.2.val)
  · rintro ⟨currentAddress,currentAddresses,currentNodes,currentStep⟩ ⟨hbound,hcurrentFrame,hcurrentFrames,hvalues⟩
    dsimp only at hbound hcurrentFrame hcurrentFrames hvalues
    dsimp only
    by_cases hrun : currentStep.val < 3
    · apply WP.spec_mono (round_body_spec currentAddress currentAddresses currentNodes digits offset currentStep seed key
        hrun hoffset hcurrentFrame hcurrentFrames)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextAddresses,nextNodes,nextStep⟩
        rcases hresult with ⟨hnext,hnextFrame,hnextFrames,hnextValues⟩
        dsimp only
        refine ⟨⟨by omega,hnextFrame,hnextFrames,?_⟩,by omega⟩
        intro j hj
        let chain : Fin EthLib.Cryptography.Sphincs.Constants.V := ⟨offset.val+j,by change offset.val+j < 64; omega⟩
        have hd := hdigits chain
        dsimp only [chain] at hd
        rw [hnextValues j hj,hvalues j hj,hnext,progress]
        simp only [eligible,hd]
    · have hstep : currentStep.val = 3 := by omega
      have hstop : ¬currentStep < lean_sphincs.params.CHAIN_END := by
        simp only [lean_sphincs.params.CHAIN_END]
        scalar_tac
      simp only [lean_sphincs.wots.recover_window_loop0.body,ite_eq_right hstop,WP.spec_ok]
      refine ⟨hcurrentFrame,hcurrentFrames,?_⟩
      intro j hj
      rw [hvalues j hj,hstep,progress_end]
  · refine ⟨by scalar_tac,hframe,hframes,?_⟩
    intro j hj
    rfl

end RustCrypto.WotsAvx2
