module
public import RustCrypto.PermutationBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Permutation
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem suffix_step (round : Nat) (hr : round < 24) :
    Batching.KeccakModel.indices.drop round =
      ⟨round, hr⟩ :: Batching.KeccakModel.indices.drop (round + 1) := by
  interval_cases round <;> rfl

@[step] theorem permute_loop_spec (state : State) (round : Usize) (hr : round.val ≤ 24) :
    lean_sphincs.hash.batch.permute_loop state round ⦃ out =>
      asModel out = Batching.KeccakModel.rounds (Batching.KeccakModel.indices.drop round.val)
        (asModel state) ⦄ := by
  let expected := Batching.KeccakModel.rounds (Batching.KeccakModel.indices.drop round.val)
    (asModel state)
  unfold lean_sphincs.hash.batch.permute_loop
  apply loop.spec_decr_nat
    (fun current : State × Usize => 24 - current.2.val)
    (fun current : State × Usize => current.2.val ≤ 24 ∧
      expected = Batching.KeccakModel.rounds (Batching.KeccakModel.indices.drop current.2.val)
        (asModel current.1))
  · rintro ⟨current, cr⟩ ⟨hcr, hmodel⟩
    dsimp only at hcr hmodel
    dsimp only
    by_cases hrun : cr.val < 24
    · apply WP.spec_mono (round_body_spec current cr hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont pair =>
        rcases pair with ⟨next, nextRound⟩
        rcases hresult with ⟨hstate, hnext⟩
        have hround : asModel next =
            Batching.KeccakModel.round ⟨cr.val, hrun⟩ (asModel current) := by
          rw [hstate]
          exact asModel_round ⟨cr.val, hrun⟩ current
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [hmodel, suffix_step cr.val hrun]
        simp only [Batching.KeccakModel.rounds, List.foldl_cons]
        rw [hnext, hround]
    · have hstop : ¬ cr < lean_sphincs.hash.batch.ROUNDS := by
        simpa only [lean_sphincs.hash.batch.ROUNDS] using
          (show ¬ cr < 24#usize by scalar_tac)
      have hdone : cr.val = 24 := by omega
      simp only [lean_sphincs.hash.batch.permute_loop.body, ite_eq_right hstop, WP.spec_ok]
      simpa [expected, hdone, Batching.KeccakModel.indices, Batching.KeccakModel.rounds] using hmodel.symm
  · exact ⟨hr, rfl⟩

/-- All 24 source SIMD rounds terminate and equal the EthLib-linked permutation model. -/
@[step] theorem permute_spec (state : State) :
    lean_sphincs.hash.batch.permute state ⦃ out =>
      asModel out = Batching.KeccakModel.permute (asModel state) ⦄ := by
  unfold lean_sphincs.hash.batch.permute
  apply WP.spec_mono (permute_loop_spec state 0#usize (by simp))
  intro out hout
  simpa [Batching.KeccakModel.permute] using hout

/-- The complete source SIMD permutation equals EthLib independently in every lane. -/
@[step] theorem permute_ethlib_spec (state : State) :
    lean_sphincs.hash.batch.permute state ⦃ out => ∀ lane,
      Batching.KeccakModel.project (asModel out) lane =
        EthLib.Cryptography.Hash.Keccak.keccakF
          (Batching.KeccakModel.project (asModel state) lane) ⦄ := by
  apply WP.spec_mono (permute_spec state)
  intro out hout lane
  rw [hout, Batching.KeccakModel.project_permute]

end RustCrypto.Permutation
