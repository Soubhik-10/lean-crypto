module
public import RustCrypto.WotsScalarLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem scalar_body_short_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (index : Usize) (hindex : index.val < 64) (hreader : reader.val.length < 16) :
    lean_sphincs.wots.recover_chains_loop.body digits address reader ends index ⦃ out =>
      out = .done (none,address,reader,ends) ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop.body
  have hrun : index < lean_sphincs.params.WOTS_CHAINS := by
    simp only [lean_sphincs.params.WOTS_CHAINS]
    scalar_tac
  simp only [ite_eq_left hrun]
  rw [RustParser.take_failure 16#usize reader hreader]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]

def scalarShortInvariant (reader : Slice U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (state : Address × Slice U8 × List U8 × Usize) : Prop :=
  state.2.2.2.val ≤ 64 ∧ 16*state.2.2.2.val ≤ reader.val.length ∧
  state.2.1.val = reader.val.drop (16*state.2.2.2.val) ∧ keyFrame state.1 seed key .wotsHash

@[step] theorem scalar_short_loop_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hreader : reader.val.length < 1024) (hdigits : digitRelation digits word) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop address reader digits ends 0#usize ⦃ out =>
      out.1 = none ∧ keyFrame out.2.1 seed key .wotsHash ∧ out.2.2.1.val = reader.val.drop (16*(reader.val.length/16)) ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Usize => 64-state.2.2.2.val)
    (scalarShortInvariant reader seed key)
  · rintro ⟨currentAddress,currentReader,currentEnds,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hconsumed,hread,hcurrentFrame⟩
    dsimp only at hcount hconsumed hread hcurrentFrame
    dsimp only
    have hrun : currentIndex.val < 64 := by omega
    have hremaining : currentReader.val.length = reader.val.length-16*currentIndex.val := by rw [hread,List.length_drop]
    by_cases hsmall : currentReader.val.length < 16
    · apply WP.spec_mono (scalar_body_short_spec currentAddress currentReader currentEnds digits currentIndex hrun hsmall)
      intro result hresult
      rw [hresult]
      change none = (none : Option Unit) ∧ keyFrame currentAddress seed key .wotsHash ∧
        currentReader.val = reader.val.drop (16*(reader.val.length/16))
      refine ⟨rfl,hcurrentFrame,?_⟩
      have hc : 16*currentIndex.val = 16*(reader.val.length/16) := by omega
      rw [hread,hc]
    · apply WP.spec_mono (scalar_body_spec currentAddress currentReader currentEnds digits word seed key currentIndex hrun (by omega) hdigits hcurrentFrame)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextReader,nextEnds,nextIndex⟩
        rcases hresult with ⟨hindex,hnextReader,hnextFrame,root,hroot,hnextEnds⟩
        have hnewReader : nextReader.val = reader.val.drop (16*nextIndex.val) := by
          rw [hnextReader,hread,List.drop_drop,hindex]
          congr 1
        dsimp only
        constructor
        · dsimp only [scalarShortInvariant]
          exact ⟨by omega,by omega,hnewReader,hnextFrame⟩
        · rw [hindex]
          omega
  · change scalarShortInvariant reader seed key (address,reader,ends,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,?_,hframe⟩
    · simp only [hz,Nat.mul_zero,Nat.zero_le]
    · simp only [hz,Nat.mul_zero,List.drop_zero]

end RustCrypto.WotsRecover
