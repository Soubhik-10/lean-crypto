module
public import RustCrypto.ForsScalarShortBody
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsScalar
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def shortInvariant (reader : Slice U8) (seed : Node) (idx : Nat)
    (state : Address × Slice U8 × List U8 × Usize) : Prop :=
  state.2.2.2.val ≤ 24 ∧ 176*state.2.2.2.val ≤ reader.val.length ∧
  state.2.1.val = reader.val.drop (176*state.2.2.2.val) ∧
  keyFrame state.1 seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree

@[step] theorem short_loop_spec (address : Address) (reader : Slice U8) (roots : List U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) (hreader : reader.val.length < 4224)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop address reader digest roots 0#usize ⦃ out =>
      out.1 = none ∧ keyFrame out.2.1 seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ∧
      out.2.2.1.val = reader.val.drop (16*(reader.val.length/16)) ⦄ := by
  unfold lean_sphincs.fors.recover_trees_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Usize => 24-state.2.2.2.val)
    (shortInvariant reader seed idx)
  · rintro ⟨currentAddress,currentReader,currentRoots,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hconsumed,hread,hcurrentFrame⟩
    dsimp only at hcount hconsumed hread hcurrentFrame
    dsimp only
    have hrun : currentIndex.val < 24 := by omega
    have hremaining : currentReader.val.length = reader.val.length-176*currentIndex.val := by rw [hread,List.length_drop]
    by_cases hsmall : currentReader.val.length < 176
    · apply WP.spec_mono (body_short_spec currentAddress currentReader currentRoots digest seed idx currentIndex hrun hsmall hcurrentFrame)
      intro result hresult
      cases result with
      | cont value => exact False.elim hresult
      | done value =>
        rcases value with ⟨status,nextAddress,remaining,nextRoots⟩
        rcases hresult with ⟨hstatus,hnextFrame,hnextReader,hnextRoots⟩
        refine ⟨hstatus,hnextFrame,?_⟩
        rw [hnextReader,hread,List.length_drop,List.drop_drop]
        have hc : 176*currentIndex.val+16*((reader.val.length-176*currentIndex.val)/16) = 16*(reader.val.length/16) := by omega
        rw [hc]
    · apply WP.spec_mono (body_spec currentAddress currentReader currentRoots digest seed idx currentIndex hrun (by omega) hcurrentFrame)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextReader,nextRoots,nextIndex⟩
        rcases hresult with ⟨hindex,hnextReader,hnextFrame,root,hroot,hnextRoots⟩
        have hnewReader : nextReader.val = reader.val.drop (176*nextIndex.val) := by
          rw [hnextReader,hread,List.drop_drop,hindex]
          congr 1
        dsimp only
        constructor
        · dsimp only [shortInvariant]
          exact ⟨by omega,by omega,hnewReader,hnextFrame⟩
        · rw [hindex]
          omega
  · change shortInvariant reader seed idx (address,reader,roots,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,?_,hframe⟩
    · simp only [hz,Nat.mul_zero,Nat.zero_le]
    · simp only [hz,Nat.mul_zero,List.drop_zero]

end RustCrypto.ForsScalar
