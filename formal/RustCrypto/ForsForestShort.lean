module
public import RustCrypto.ForsForestFull
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem body_short_spec (reader : Slice U8) (roots : List U8)
    (addresses : Aeneas.Std.Array Address 2#usize) (digest : Aeneas.Std.Array U8 34#usize) (start : Usize)
    (hstart : start.val < 24) (hreader : reader.val.length < 352) :
    lean_sphincs.fors.recover_trees_loop.body digest reader roots addresses start ⦃ out =>
      out = .done (none,reader,roots) ⦄ := by
  unfold lean_sphincs.fors.recover_trees_loop.body
  have hrun : start < lean_sphincs.params.FORS_TREES := by
    simp only [lean_sphincs.params.FORS_TREES]
    scalar_tac
  simp only [ite_eq_left hrun]
  rw [RustParser.take_failure 352#usize reader hreader]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]

def shortInvariant (reader : Slice U8) (seed : Node) (idx : Nat)
    (state : Slice U8 × List U8 × Aeneas.Std.Array Address 2#usize × Usize) : Prop :=
  state.2.2.2.val ≤ 24 ∧ state.2.2.2.val % width = 0 ∧ 176*state.2.2.2.val ≤ reader.val.length ∧
  state.1.val = reader.val.drop (176*state.2.2.2.val) ∧
  (∀ j : Fin width, keyFrame (state.2.2.1[j.val]!) seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree)

/-- Every short FORS reader is rejected, after consuming exactly its complete batches. -/
@[step] theorem short_loop_spec (reader : Slice U8) (roots : List U8)
    (addresses : Aeneas.Std.Array Address 2#usize) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hreader : reader.val.length < 4224)
    (hframes : ∀ j : Fin width, keyFrame (addresses[j.val]!) seed
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop reader digest roots addresses 0#usize ⦃ out =>
      out.1 = none ∧ out.2.1.val = reader.val.drop (352*(reader.val.length/352)) ⦄ := by
  unfold lean_sphincs.fors.recover_trees_loop
  apply loop.spec_decr_nat
    (fun state : Slice U8 × List U8 × Aeneas.Std.Array Address 2#usize × Usize => 24-state.2.2.2.val)
    (shortInvariant reader seed idx)
  · rintro ⟨currentReader,currentRoots,currentAddresses,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hmod,hconsumed,hread,hcurrentFrames⟩
    dsimp only at hcount hmod hconsumed hread hcurrentFrames
    dsimp only
    have hrun : currentIndex.val < 24 := by omega
    have hremaining : currentReader.val.length = reader.val.length - 176*currentIndex.val := by
      rw [hread,List.length_drop]
    by_cases hsmall : currentReader.val.length < 352
    · apply WP.spec_mono (body_short_spec currentReader currentRoots currentAddresses digest currentIndex hrun hsmall)
      intro result hresult
      rw [hresult]
      change none = (none : Option Unit) ∧ currentReader.val = reader.val.drop (352*(reader.val.length/352))
      refine ⟨rfl,?_⟩
      have hc : 176*currentIndex.val = 352*(reader.val.length/352) := by
        simp only [width] at hmod
        omega
      rw [hread,hc]
    · have hstart : currentIndex.val+width ≤ 24 := by
        simp only [width] at hmod ⊢
        omega
      apply WP.spec_mono (forest_body_spec currentReader currentRoots currentAddresses digest seed idx currentIndex hstart (by omega) hcurrentFrames)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextReader,nextRoots,nextAddresses,nextIndex⟩
        rcases hresult with ⟨hindex,hnextReader,nodes,hnextRoots,hnodes,hnextFrames⟩
        have hnewReader : nextReader.val = reader.val.drop (176*nextIndex.val) := by
          rw [hnextReader,hread,List.drop_drop,hindex]
          congr 1
        dsimp only
        constructor
        · dsimp only [shortInvariant]
          refine ⟨by omega,?_,?_,hnewReader,hnextFrames⟩
          · rw [hindex]
            simp only [width] at hmod ⊢
            omega
          · rw [hindex]
            simp only [width]
            omega
        · rw [hindex]
          have hw : 0 < width := by decide
          omega
  · change shortInvariant reader seed idx (reader,roots,addresses,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,?_,?_,hframes⟩
    · simp only [hz,Nat.zero_mod]
    · simp only [hz,Nat.mul_zero,Nat.zero_le]
    · simp only [hz,Nat.mul_zero,List.drop_zero]

end RustCrypto.ForsForest
