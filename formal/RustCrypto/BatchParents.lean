module
public import RustCrypto.BatchNodes
@[expose] public section
open Aeneas Aeneas.Std Result
open RustCrypto.BatchNodes
namespace RustCrypto.BatchParents
set_option maxHeartbeats 2000000

def parentBytes (address : Address) (value sibling : Node) (position : U32) : List U8 :=
  let right := (position &&& 1#u32) != 0#u32
  (address.val.setSlice! 48 (if right then sibling.val else value.val)).setSlice!
    64 (if right then value.val else sibling.val)

@[step] theorem parent_body_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (values siblings : Aeneas.Std.Array Node 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize)
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize)
    (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.hash.HashContext.hash_parents_loop.body values siblings positions addresses inputs lane ⦃ result =>
      match result with
      | .cont (nextAddresses,nextInputs,nextLane) =>
          nextLane.val = lane.val+1 ∧
          (∀ j < 2, (nextAddresses[j]!).val = if j = lane.val then
            parentBytes (addresses[lane.val]!) (values[lane.val]!) (siblings[lane.val]!) (positions[lane.val]!)
            else (addresses[j]!).val) ∧
          (∀ j < 2, (nextInputs[j]!).val = if j = lane.val then
            parentBytes (addresses[lane.val]!) (values[lane.val]!) (siblings[lane.val]!) (positions[lane.val]!)
            else (inputs[j]!).val)
      | .done _ => False ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_parents_loop.body
  simp only [lean_sphincs.hash.batch.WIDTH]
  have hbranch : lane < 2#usize := by scalar_tac
  simp only [ite_eq_left hbranch]
  step*
  have haddress : hc = addresses[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos addresses.val lane.val (by scalar_tac)]
    exact hc_post
  have hvalue : fb = values[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos values.val lane.val (by scalar_tac)]
    exact fb_post
  have hsibling : fb1 = siblings[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos siblings.val lane.val (by scalar_tac)]
    exact fb1_post
  have hposition : i = positions[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos positions.val lane.val (by scalar_tac)]
    exact i_post
  have hbit : i1 = i &&& 1#u32 := by scalar_tac
  refine ⟨lane1_post, ?_, ?_⟩
  · intro j hj
    rw [index_mut_back_post, array_set_read addresses lane hc1 j (by scalar_tac)]
    by_cases heq : j = lane.val
    · simp only [ite_eq_left heq]
      rw [← a_post]
      simpa only [parentBytes, haddress, hvalue, hsibling, hbit, hposition] using a_post1
    · simp only [ite_eq_right heq]
  · intro j hj
    rw [a1_post, array_set_read inputs lane a j (by scalar_tac)]
    by_cases heq : j = lane.val
    · simp only [ite_eq_left heq]
      simpa only [parentBytes, haddress, hvalue, hsibling, hbit, hposition] using a_post1
    · simp only [ite_eq_right heq]


@[step] theorem parent_loop_spec (original addresses : Aeneas.Std.Array Address 2#usize)
    (values siblings : Aeneas.Std.Array Node 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize)
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize)
    (lane : Usize) (hlane : lane.val ≤ 2)
    (ha : ∀ j < 2, (addresses[j]!).val = if j < lane.val then
      parentBytes (original[j]!) (values[j]!) (siblings[j]!) (positions[j]!) else (original[j]!).val)
    (hi : ∀ j < lane.val, (inputs[j]!).val =
      parentBytes (original[j]!) (values[j]!) (siblings[j]!) (positions[j]!)) :
    lean_sphincs.hash.HashContext.hash_parents_loop addresses values siblings positions inputs lane ⦃ out =>
      (∀ j < 2, (out.1[j]!).val = parentBytes (original[j]!) (values[j]!) (siblings[j]!) (positions[j]!)) ∧
      (∀ j < 2, (out.2[j]!).val = parentBytes (original[j]!) (values[j]!) (siblings[j]!) (positions[j]!)) ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_parents_loop
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Address 2#usize ×
      Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize × Usize => 2-state.2.2.val)
    (fun state : Aeneas.Std.Array Address 2#usize ×
      Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize × Usize =>
      state.2.2.val ≤ 2 ∧
      (∀ j < 2, (state.1[j]!).val = if j < state.2.2.val then
        parentBytes (original[j]!) (values[j]!) (siblings[j]!) (positions[j]!) else (original[j]!).val) ∧
      (∀ j < state.2.2.val, (state.2.1[j]!).val =
        parentBytes (original[j]!) (values[j]!) (siblings[j]!) (positions[j]!)))
  · rintro ⟨currentAddresses,currentInputs,currentLane⟩ ⟨hbound,haddr,hinput⟩
    dsimp only at hbound haddr hinput
    dsimp only
    by_cases hrun : currentLane.val < 2
    · have hactive : (currentAddresses[currentLane.val]!).val =
          (original[currentLane.val]!).val := by
        simpa only [ite_eq_right (Nat.lt_irrefl currentLane.val)] using haddr currentLane.val hrun
      apply WP.spec_mono (parent_body_spec currentAddresses values siblings positions currentInputs currentLane hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddresses,nextInputs,nextLane⟩
        rcases hresult with ⟨hnext,hanext,hinext⟩
        dsimp only
        refine ⟨⟨by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
        · intro j hj
          have hupdate := hanext j hj
          by_cases heq : j = currentLane.val
          · subst j
            have hbefore : currentLane.val < nextLane.val := by scalar_tac
            simpa only [ite_self, ite_true, ite_eq_left hbefore, parentBytes, hactive] using hupdate
          · have hcut : j < nextLane.val ↔ j < currentLane.val := by scalar_tac
            rw [ite_eq_right heq] at hupdate
            rw [hupdate]
            simpa only [hcut] using haddr j hj
        · intro j hj
          have hj2 : j < 2 := by scalar_tac
          have hupdate := hinext j hj2
          by_cases heq : j = currentLane.val
          · subst j
            simpa only [ite_self, ite_true, parentBytes, hactive] using hupdate
          · have hbefore : j < currentLane.val := by scalar_tac
            rw [ite_eq_right heq] at hupdate
            exact hupdate.trans (hinput j hbefore)
    · have hdone : currentLane.val = 2 := by omega
      have hstop : ¬ currentLane < lean_sphincs.hash.batch.WIDTH := by
        simp only [lean_sphincs.hash.batch.WIDTH]
        scalar_tac
      simp only [lean_sphincs.hash.HashContext.hash_parents_loop.body, ite_eq_right hstop, WP.spec_ok]
      constructor
      · intro j hj
        simpa only [hdone, ite_eq_left hj] using haddr j hj
      · intro j hj
        exact hinput j (by simpa only [hdone] using hj)
  · exact ⟨hlane, ha, hi⟩


/-- Complete source parent batching preserves each lane's address and sibling order. -/
@[step] theorem hash_parents_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (values siblings : Aeneas.Std.Array Node 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize) :
    lean_sphincs.hash.HashContext.hash_parents addresses values siblings positions ⦃ out =>
      (∀ j < 2, (out.1[j]!).val = (RustCrypto.digest
        (parentBytes (addresses[j]!) (values[j]!) (siblings[j]!) (positions[j]!))).val.take 16) ∧
      (∀ j < 2, (out.2[j]!).val =
        parentBytes (addresses[j]!) (values[j]!) (siblings[j]!) (positions[j]!)) ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_parents
  step with parent_loop_spec addresses addresses values siblings positions _ 0#usize (by decide)
    (by intro j hj; simp) (by intro j hj; scalar_tac)
  step with RustCrypto.ShortHash.hash_80_bytes_spec
  constructor
  · intro j hj
    simpa only [out_post1 j hj] using a1_post ⟨j,hj⟩
  · exact out_post

end RustCrypto.BatchParents
