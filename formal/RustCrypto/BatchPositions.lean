module
public import RustCrypto.BatchNodes
@[expose] public section
open Aeneas Aeneas.Std Result
open RustCrypto.BatchNodes
namespace RustCrypto.BatchPositions
set_option maxHeartbeats 2000000

def addressBytes (address : Address) (height position : U32) : List U8 :=
  address.val.take 40 ++ (core.num.U32.to_be_bytes height).val ++
    (core.num.U32.to_be_bytes position).val ++ address.val.drop 48

@[step] theorem body_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (height : U32) (positions : Aeneas.Std.Array U32 2#usize)
    (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.hash.HashContext.set_positions_loop.body height positions addresses lane ⦃ result =>
      match result with
      | .cont (out,next) => next.val = lane.val+1 ∧ ∀ j < 2,
          (out[j]!).val = if j = lane.val then
            addressBytes (addresses[lane.val]!) height (positions[lane.val]!)
          else (addresses[j]!).val
      | .done _ => False ⦄ := by
  unfold lean_sphincs.hash.HashContext.set_positions_loop.body
  simp only [lean_sphincs.hash.batch.WIDTH]
  have hbranch : lane < 2#usize := by scalar_tac
  simp only [ite_eq_left hbranch]
  step*
  have haddress : hc = addresses[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos addresses.val lane.val (by scalar_tac)]
    exact hc_post
  have hposition : i = positions[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos positions.val lane.val (by scalar_tac)]
    exact i_post
  refine ⟨lane1_post, ?_⟩
  intro j hj
  rw [index_mut_back_post, array_set_read addresses lane hc1 j (by scalar_tac)]
  by_cases heq : j = lane.val
  · simp only [ite_eq_left heq]
    simpa only [addressBytes, haddress, hposition] using hc1_post
  · simp only [ite_eq_right heq]

@[step] theorem loop_spec (original addresses : Aeneas.Std.Array Address 2#usize)
    (height : U32) (positions : Aeneas.Std.Array U32 2#usize)
    (lane : Usize) (hlane : lane.val ≤ 2)
    (ha : ∀ j < 2, (addresses[j]!).val = if j < lane.val then
      addressBytes (original[j]!) height (positions[j]!) else (original[j]!).val) :
    lean_sphincs.hash.HashContext.set_positions_loop addresses height positions lane ⦃ out =>
      ∀ j < 2, (out[j]!).val = addressBytes (original[j]!) height (positions[j]!) ⦄ := by
  unfold lean_sphincs.hash.HashContext.set_positions_loop
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Address 2#usize × Usize => 2-state.2.val)
    (fun state : Aeneas.Std.Array Address 2#usize × Usize => state.2.val ≤ 2 ∧
      ∀ j < 2, (state.1[j]!).val = if j < state.2.val then
        addressBytes (original[j]!) height (positions[j]!) else (original[j]!).val)
  · rintro ⟨currentAddresses,currentLane⟩ ⟨hbound,haddr⟩
    dsimp only at hbound haddr
    dsimp only
    by_cases hrun : currentLane.val < 2
    · have hactive : (currentAddresses[currentLane.val]!).val =
          (original[currentLane.val]!).val := by
        simpa only [ite_eq_right (Nat.lt_irrefl currentLane.val)] using haddr currentLane.val hrun
      apply WP.spec_mono (body_spec currentAddresses height positions currentLane hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddresses,nextLane⟩
        rcases hresult with ⟨hnext,hanext⟩
        dsimp only
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        intro j hj
        have hupdate := hanext j hj
        by_cases heq : j = currentLane.val
        · subst j
          have hbefore : currentLane.val < nextLane.val := by scalar_tac
          simpa only [ite_self, ite_true, ite_eq_left hbefore, addressBytes, hactive] using hupdate
        · have hcut : j < nextLane.val ↔ j < currentLane.val := by scalar_tac
          rw [ite_eq_right heq] at hupdate
          rw [hupdate]
          simpa only [hcut] using haddr j hj
    · have hdone : currentLane.val = 2 := by omega
      have hstop : ¬ currentLane < lean_sphincs.hash.batch.WIDTH := by
        simp only [lean_sphincs.hash.batch.WIDTH]
        scalar_tac
      simp only [lean_sphincs.hash.HashContext.set_positions_loop.body, ite_eq_right hstop, WP.spec_ok]
      intro j hj
      simpa only [hdone, ite_eq_left hj] using haddr j hj
  · exact ⟨hlane, ha⟩

@[step] theorem set_positions_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (height : U32) (positions : Aeneas.Std.Array U32 2#usize) :
    lean_sphincs.hash.HashContext.set_positions addresses height positions ⦃ out =>
      ∀ j < 2, (out[j]!).val = addressBytes (addresses[j]!) height (positions[j]!) ⦄ := by
  unfold lean_sphincs.hash.HashContext.set_positions
  exact loop_spec addresses addresses height positions 0#usize (by decide) (by intro j hj; simp)

end RustCrypto.BatchPositions
