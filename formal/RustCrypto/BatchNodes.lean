module
public import RustCrypto.ShortHash
public import RustCrypto.HashPrimitives
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BatchNodes
set_option maxHeartbeats 2000000
abbrev Node := Aeneas.Std.Array U8 16#usize
abbrev Address := lean_sphincs.hash.HashContext

@[simp] theorem array_set_read {T : Type} [Inhabited T] {n : Usize}
    (input : Aeneas.Std.Array T n) (index : Usize) (value : T) (j : Nat) (hj : j < n.val) :
    (input.set index value)[j]! = if j = index.val then value else input[j]! := by
  by_cases heq : j = index.val
  · simp only [ite_eq_left heq]
    exact Aeneas.Std.Array.getElem!_Nat_set_eq input index j value ⟨heq.symm, by simpa using hj⟩
  · simp only [ite_eq_right heq]
    exact Aeneas.Std.Array.getElem!_Nat_set_ne input index j value (Ne.symm heq)

@[step] theorem node_body_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (values : Aeneas.Std.Array Node 2#usize)
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize)
    (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.hash.HashContext.hash_nodes_loop.body values addresses inputs lane ⦃ result =>
      match result with
      | .cont (nextAddresses,nextInputs,nextLane) =>
          nextLane.val = lane.val+1 ∧
          (∀ j < 2, (nextAddresses[j]!).val = if j = lane.val then
            (addresses[lane.val]!).val.setSlice! 48 (values[lane.val]!).val
            else (addresses[j]!).val) ∧
          (∀ j < 2, (nextInputs[j]!).val = if j = lane.val then
            (addresses[lane.val]!).val.take 48 ++ (values[lane.val]!).val
            else (inputs[j]!).val)
      | .done _ => False ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_nodes_loop.body
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
  refine ⟨lane1_post, ?_, ?_⟩
  · intro j hj
    rw [index_mut_back_post, array_set_read addresses lane hc1 j (by scalar_tac)]
    by_cases heq : j = lane.val
    · simp only [ite_eq_left heq]
      simpa only [haddress, hvalue] using a_post1
    · simp only [ite_eq_right heq]
  · intro j hj
    rw [a1_post, array_set_read inputs lane a j (by scalar_tac)]
    by_cases heq : j = lane.val
    · simp only [ite_eq_left heq]
      simpa only [haddress, hvalue] using a_post
    · simp only [ite_eq_right heq]


@[step] theorem node_loop_spec (original addresses : Aeneas.Std.Array Address 2#usize)
    (values : Aeneas.Std.Array Node 2#usize)
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize)
    (lane : Usize) (hlane : lane.val ≤ 2)
    (ha : ∀ j < 2, (addresses[j]!).val = if j < lane.val then
      (original[j]!).val.setSlice! 48 (values[j]!).val else (original[j]!).val)
    (hi : ∀ j < lane.val, (inputs[j]!).val =
      (original[j]!).val.take 48 ++ (values[j]!).val) :
    lean_sphincs.hash.HashContext.hash_nodes_loop addresses values inputs lane ⦃ out =>
      (∀ j < 2, (out.1[j]!).val = (original[j]!).val.setSlice! 48 (values[j]!).val) ∧
      (∀ j < 2, (out.2[j]!).val = (original[j]!).val.take 48 ++ (values[j]!).val) ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_nodes_loop
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Address 2#usize ×
      Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize × Usize => 2-state.2.2.val)
    (fun state : Aeneas.Std.Array Address 2#usize ×
      Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize × Usize =>
      state.2.2.val ≤ 2 ∧
      (∀ j < 2, (state.1[j]!).val = if j < state.2.2.val then
        (original[j]!).val.setSlice! 48 (values[j]!).val else (original[j]!).val) ∧
      (∀ j < state.2.2.val, (state.2.1[j]!).val =
        (original[j]!).val.take 48 ++ (values[j]!).val))
  · rintro ⟨currentAddresses,currentInputs,currentLane⟩ ⟨hbound,haddr,hinput⟩
    dsimp only at hbound haddr hinput
    dsimp only
    by_cases hrun : currentLane.val < 2
    · have hactive : (currentAddresses[currentLane.val]!).val =
          (original[currentLane.val]!).val := by
        simpa only [ite_eq_right (Nat.lt_irrefl currentLane.val)] using haddr currentLane.val hrun
      apply WP.spec_mono (node_body_spec currentAddresses values currentInputs currentLane hrun)
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
            simpa only [ite_self, ite_true, ite_eq_left hbefore, hactive] using hupdate
          · have hcut : j < nextLane.val ↔ j < currentLane.val := by scalar_tac
            rw [ite_eq_right heq] at hupdate
            rw [hupdate]
            simpa only [hcut] using haddr j hj
        · intro j hj
          have hj2 : j < 2 := by scalar_tac
          have hupdate := hinext j hj2
          by_cases heq : j = currentLane.val
          · subst j
            simpa only [ite_self, ite_true, hactive] using hupdate
          · have hbefore : j < currentLane.val := by scalar_tac
            rw [ite_eq_right heq] at hupdate
            exact hupdate.trans (hinput j hbefore)
    · have hdone : currentLane.val = 2 := by omega
      have hstop : ¬ currentLane < lean_sphincs.hash.batch.WIDTH := by
        simp only [lean_sphincs.hash.batch.WIDTH]
        scalar_tac
      simp only [lean_sphincs.hash.HashContext.hash_nodes_loop.body, ite_eq_right hstop, WP.spec_ok]
      constructor
      · intro j hj
        simpa only [hdone, ite_eq_left hj] using haddr j hj
      · intro j hj
        exact hinput j (by simpa only [hdone] using hj)
  · exact ⟨hlane, ha, hi⟩

/-- Every actual SIMD node-hash lane uses its own seed/address and node bytes. -/
@[step] theorem hash_nodes_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (values : Aeneas.Std.Array Node 2#usize) :
    lean_sphincs.hash.HashContext.hash_nodes addresses values ⦃ out =>
      (∀ j < 2, (out.1[j]!).val =
        (RustCrypto.digest ((addresses[j]!).val.take 48 ++ (values[j]!).val)).val.take 16) ∧
      (∀ j < 2, (out.2[j]!).val = (addresses[j]!).val.setSlice! 48 (values[j]!).val) ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_nodes
  step with node_loop_spec addresses addresses values _ 0#usize (by decide)
    (by intro j hj; simp) (by intro j hj; scalar_tac)
  step with RustCrypto.ShortHash.hash_64_bytes_spec
  constructor
  · intro j hj
    simpa only [out_post1 j hj] using a1_post ⟨j,hj⟩
  · exact out_post

end RustCrypto.BatchNodes
