module
public import RustCrypto.WotsAvx2ChainsLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem chains_body_short_spec (address : Address) (reader : Slice U8) (ends : List U8)
    (addresses : Aeneas.Std.Array Address 4#usize) (digits : WotsRecover.Digits) (window : Usize)
    (hwindow : window.val < 4) (hreader : reader.val.length < 256) :
    lean_sphincs.wots.recover_chains_loop.body digits address reader ends addresses window ⦃ out =>
      out = .done (none,address,reader,ends) ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop.body
  simp only [lean_sphincs.params.WOTS_CHAINS,lean_sphincs.wots.CHAINS_PER_WINDOW]
  step as ⟨bound,hbound⟩
  have hb : bound.val = 4 := by scalar_tac
  have hrun : window < bound := by scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨offset,hoffset⟩
  step with read_window_short_spec reader hreader as ⟨option,remaining,hoption,hremaining⟩
  rw [hoption,hremaining]
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]

def shortInvariant (reader : Slice U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (state : Address × Slice U8 × List U8 × Aeneas.Std.Array Address 4#usize × Usize) : Prop :=
  state.2.2.2.2.val ≤ 4 ∧ 256*state.2.2.2.2.val ≤ reader.val.length ∧
  state.2.1.val = reader.val.drop (256*state.2.2.2.2.val) ∧ keyFrame state.1 seed key .wotsHash ∧
  ∀ j < 4, keyFrame (state.2.2.2.1[j]!) seed key .wotsHash

/-- Short inputs consume complete windows and leave every byte of the incomplete window unread. -/
@[step] theorem chains_short_loop_spec (address : Address) (reader : Slice U8) (ends : List U8)
    (addresses : Aeneas.Std.Array Address 4#usize) (digits : WotsRecover.Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hreader : reader.val.length < 1024) (hdigits : WotsRecover.digitRelation digits word)
    (hframe : keyFrame address seed key .wotsHash)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop address reader digits ends addresses 0#usize ⦃ out =>
      out.1 = none ∧ keyFrame out.2.1 seed key .wotsHash ∧
      out.2.2.1.val = reader.val.drop (256*(reader.val.length/256)) ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Aeneas.Std.Array Address 4#usize × Usize => 4-state.2.2.2.2.val)
    (shortInvariant reader seed key)
  · rintro ⟨currentAddress,currentReader,currentEnds,currentAddresses,currentWindow⟩ hinv
    rcases hinv with ⟨hcount,hconsumed,hread,hcurrentFrame,hcurrentFrames⟩
    dsimp only at hcount hconsumed hread hcurrentFrame hcurrentFrames
    dsimp only
    have hrun : currentWindow.val < 4 := by omega
    have hremaining : currentReader.val.length = reader.val.length-256*currentWindow.val := by
      rw [hread,List.length_drop]
    by_cases hsmall : currentReader.val.length < 256
    · apply WP.spec_mono (chains_body_short_spec currentAddress currentReader currentEnds currentAddresses digits currentWindow hrun hsmall)
      intro result hresult
      rw [hresult]
      change none = (none : Option Unit) ∧ keyFrame currentAddress seed key .wotsHash ∧
        currentReader.val = reader.val.drop (256*(reader.val.length/256))
      refine ⟨rfl,hcurrentFrame,?_⟩
      have hc : 256*currentWindow.val = 256*(reader.val.length/256) := by omega
      rw [hread,hc]
    · apply WP.spec_mono (chains_body_spec currentAddress currentReader currentEnds currentAddresses digits word currentWindow
        seed key hrun (by omega) hdigits hcurrentFrame hcurrentFrames)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextReader,nextEnds,nextAddresses,nextWindow⟩
        rcases hresult with ⟨hwindow,hnextReader,hnextFrame,hnextFrames,roots,hnextEnds,hroots⟩
        dsimp only [shortInvariant]
        refine ⟨⟨by omega,by omega,?_,hnextFrame,hnextFrames⟩,by omega⟩
        rw [hnextReader,hread,List.drop_drop,hwindow]
        congr 1
  · change shortInvariant reader seed key (address,reader,ends,addresses,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,by simp only [hz,Nat.mul_zero,Nat.zero_le],?_,hframe,hframes⟩
    simp only [hz,Nat.mul_zero,List.drop_zero]

end RustCrypto.WotsAvx2
