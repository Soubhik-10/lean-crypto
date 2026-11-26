module
public import RustCrypto.WotsRecoverModel
public import RustCrypto.BatchPositions
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def groupAddress (address : Address) (selected offset : Usize) (step : U8) : Address :=
  positioned address (stepWord (offset.val+selected.val)) (stepWord step.val)

@[step] theorem position_body_spec (addresses : Aeneas.Std.Array Address 4#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (offset : Usize) (step : U8) (lane : Usize)
    (hlane : lane.val < 4) (hchains : ∀ j < 4, (chains[j]!).val < 16) (hoffset : offset.val+16 ≤ 64) :
    lean_sphincs.wots.recover_group_loop0.body chains offset step addresses lane ⦃ out =>
      match out with
      | .done _ => False
      | .cont (next,nextLane) => nextLane.val = lane.val+1 ∧
          next = addresses.set lane (groupAddress (addresses[lane.val]!) (chains[lane.val]!) offset step) ⦄ := by
  unfold lean_sphincs.wots.recover_group_loop0.body
  have hrun : lane < lean_sphincs.hash.batch.WIDTH := by
    simp only [lean_sphincs.hash.batch.WIDTH]
    scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨current,restore,hcurrent,hrestore⟩
  step as ⟨selected,hselected⟩
  have hselectedEq : selected = chains[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos chains.val lane.val (by scalar_tac)]
    exact hselected
  have hselectedBound : selected.val < 16 := by rw [hselectedEq]; exact hchains lane.val hlane
  step as ⟨sum,hsum⟩
  step as ⟨chainWord,hchainWord⟩
  step with widen_step_spec step as ⟨stepWordValue,hstepWord⟩
  step with RustCrypto.set_position_spec current chainWord stepWordValue as ⟨updated,hupdated⟩
  step as ⟨nextLane,hnextLane⟩
  have hc : current = addresses[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos addresses.val lane.val (by scalar_tac)]
    exact hcurrent
  have hchainEq : chainWord = stepWord (offset.val+selected.val) := by
    apply UScalar.eq_of_val_eq
    change chainWord.val = (offset.val+selected.val)%4294967296
    rw [Nat.mod_eq_of_lt (by omega)]
    scalar_tac
  have hstepEq : stepWordValue = stepWord step.val := by
    apply UScalar.eq_of_val_eq
    change stepWordValue.val = step.val%4294967296
    rw [Nat.mod_eq_of_lt (by scalar_tac)]
    exact hstepWord
  have hu : updated = groupAddress (addresses[lane.val]!) (chains[lane.val]!) offset step := by
    apply Aeneas.Std.Array.ext
    simpa only [groupAddress,positioned,Aeneas.Std.Array.from_val,hc,hchainEq,hstepEq,hselectedEq] using hupdated
  refine ⟨hnextLane,?_⟩
  rw [hrestore,hu]

@[step] theorem position_loop_spec (original addresses : Aeneas.Std.Array Address 4#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (offset : Usize) (step : U8) (lane : Usize)
    (hlane : lane.val ≤ 4) (hchains : ∀ j < 4, (chains[j]!).val < 16) (hoffset : offset.val+16 ≤ 64)
    (ha : ∀ j < 4, addresses[j]! = if j < lane.val then groupAddress (original[j]!) (chains[j]!) offset step else original[j]!) :
    lean_sphincs.wots.recover_group_loop0 addresses chains offset step lane ⦃ out =>
      ∀ j < 4, out[j]! = groupAddress (original[j]!) (chains[j]!) offset step ⦄ := by
  unfold lean_sphincs.wots.recover_group_loop0
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Address 4#usize × Usize => 4-state.2.val)
    (fun state => state.2.val ≤ 4 ∧ ∀ j < 4, state.1[j]! =
      if j < state.2.val then groupAddress (original[j]!) (chains[j]!) offset step else original[j]!)
  · rintro ⟨current,currentLane⟩ ⟨hbound,haddr⟩
    dsimp only at hbound haddr
    dsimp only
    by_cases hrun : currentLane.val < 4
    · have hactive : current[currentLane.val]! = original[currentLane.val]! := by
        simpa only [ite_eq_right (Nat.lt_irrefl currentLane.val)] using haddr currentLane.val hrun
      apply WP.spec_mono (position_body_spec current chains offset step currentLane hrun hchains hoffset)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨next,nextLane⟩
        rcases hresult with ⟨hnextLane,hnext⟩
        dsimp only
        refine ⟨⟨by omega,?_⟩,by omega⟩
        intro j hj
        rw [hnext,BatchNodes.array_set_read current currentLane _ j (by scalar_tac)]
        by_cases heq : j = currentLane.val
        · subst j
          have hbefore : currentLane.val < nextLane.val := by omega
          simp only [ite_true,ite_eq_left hbefore,hactive]
        · have hcut : j < nextLane.val ↔ j < currentLane.val := by omega
          simp only [ite_eq_right heq]
          simpa only [hcut] using haddr j hj
    · have hc : currentLane.val = 4 := by omega
      have hstop : ¬currentLane < lean_sphincs.hash.batch.WIDTH := by
        simp only [lean_sphincs.hash.batch.WIDTH]
        scalar_tac
      simp only [lean_sphincs.wots.recover_group_loop0.body,ite_eq_right hstop,WP.spec_ok]
      intro j hj
      simpa only [hc,ite_eq_left hj] using haddr j hj
  · exact ⟨hlane,ha⟩

@[step] theorem position_group_spec (addresses : Aeneas.Std.Array Address 4#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (offset : Usize) (step : U8)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) (hoffset : offset.val+16 ≤ 64) :
    lean_sphincs.wots.recover_group_loop0 addresses chains offset step 0#usize ⦃ out =>
      ∀ j < 4, out[j]! = groupAddress (addresses[j]!) (chains[j]!) offset step ⦄ := by
  exact position_loop_spec addresses addresses chains offset step 0#usize (by decide) hchains hoffset
    (by intro j hj; simp)

end RustCrypto.WotsAvx2
