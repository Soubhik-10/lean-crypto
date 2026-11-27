module
public import RustCrypto.Hash.Primitives
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsChain
set_option maxHeartbeats 2000000

abbrev Node := Aeneas.Std.Array U8 16#usize
abbrev Address := lean_sphincs.hash.HashContext

def positioned (address : Address) (chain step : U32) : Address :=
  Aeneas.Std.Array.from (address.val.take 40 ++ (core.num.U32.to_be_bytes chain).val ++
    (core.num.U32.to_be_bytes step).val ++ address.val.drop 48) (by simp)

def stepWord (step : Nat) : U32 := ⟨BitVec.ofNat 32 step⟩

def nodeStep (address : Address) (chain : U32) (step : Nat) (node : Node) : Node × Address :=
  let current := positioned address chain (stepWord step)
  let output : Node := Aeneas.Std.Array.from
    ((digest (current.val.take 48 ++ node.val)).val.take 16) (by simp)
  (output, current.setSlice! 48 node.val)

@[step] theorem widen_step_spec (step : U8) :
    lift (core.convert.num.FromU32U8.from step) ⦃ out => out.val = step.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact core.convert.num.FromU32U8.from_val_eq step

@[step] theorem walk_body_spec (address : Address) (chain : U32) (stop step : U8) (node : Node)
    (hrun : step.val < stop.val) :
    lean_sphincs.wots.walk_chain_loop.body chain stop address node step ⦃ out =>
      match out with
      | .cont (nextAddress, nextNode, nextStep) =>
          (nextNode, nextAddress) = nodeStep address chain step.val node ∧
          nextStep.val = step.val + 1
      | .done _ => False ⦄ := by
  unfold lean_sphincs.wots.walk_chain_loop.body
  have hbranch : step < stop := by scalar_tac
  simp only [ite_eq_left hbranch]
  step*
  have hi : i = stepWord step.val := by
    apply UScalar.eq_of_val_eq
    have hbound : step.val < 4294967296 := by scalar_tac
    change i.val = step.val % 4294967296
    rw [Nat.mod_eq_of_lt hbound]
    exact i_post
  have haddress : address1 = positioned address chain (stepWord step.val) := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned, Aeneas.Std.Array.from_val, hi] using address1_post
  refine ⟨?_, step1_post⟩
  apply Prod.ext
  · apply Aeneas.Std.Array.ext
    simpa only [nodeStep, Aeneas.Std.Array.from_val, haddress] using node1_post
  · apply Aeneas.Std.Array.ext
    simpa only [nodeStep, Aeneas.Std.Array.setSlice!_val, haddress] using
      (by assumption : address2.val = address1.val.setSlice! 48 node.val)


def walk : Nat → Nat → U32 → Address → Node → Node × Address
  | 0, _, _, address, node => (node, address)
  | fuel + 1, step, chain, address, node =>
      let next := nodeStep address chain step node
      walk fuel (step+1) chain next.2 next.1

/-- The complete source chain walk terminates and performs exactly its specified Keccak steps. -/
@[step] theorem walk_loop_spec (address : Address) (chain : U32) (stop step : U8) (node : Node) :
    lean_sphincs.wots.walk_chain_loop address chain stop node step ⦃ out =>
      out = walk (stop.val - step.val) step.val chain address node ⦄ := by
  let expected := walk (stop.val - step.val) step.val chain address node
  unfold lean_sphincs.wots.walk_chain_loop
  apply loop.spec_decr_nat
    (fun state : Address × Node × U8 => stop.val - state.2.2.val)
    (fun state : Address × Node × U8 =>
      expected = walk (stop.val - state.2.2.val) state.2.2.val chain state.1 state.2.1)
  · rintro ⟨currentAddress, currentNode, currentStep⟩ hmodel
    dsimp only at hmodel
    dsimp only
    by_cases hrun : currentStep.val < stop.val
    · apply WP.spec_mono (walk_body_spec currentAddress chain stop currentStep currentNode hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress, nextNode, nextStep⟩
        rcases hresult with ⟨hnext, hs⟩
        refine ⟨?_, by scalar_tac⟩
        rw [hmodel]
        have hf : stop.val - currentStep.val = (stop.val - (currentStep.val+1))+1 := by omega
        rw [hf, walk, ← hnext]
        simp only [hs]
    · have hstop : ¬ currentStep < stop := by scalar_tac
      have hz : stop.val - currentStep.val = 0 := by omega
      simp only [lean_sphincs.wots.walk_chain_loop.body, ite_eq_right hstop, WP.spec_ok]
      simpa only [hz, walk] using hmodel.symm
  · rfl

@[step] theorem walk_chain_spec (address : Address) (chain : U32) (start stop : U8) (node : Node) :
    lean_sphincs.wots.walk_chain address chain start stop node ⦃ out =>
      out = walk (stop.val - start.val) start.val chain address node ⦄ := by
  exact walk_loop_spec address chain stop start node

end RustCrypto.WotsChain
