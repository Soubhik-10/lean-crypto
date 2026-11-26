module
public import RustCrypto.WotsChain
public import RustParser
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Climb
open RustCrypto.WotsChain
set_option maxHeartbeats 2000000

@[step] theorem take_node_success (reader : Slice U8) (h : 16 ≤ reader.val.length) :
    lean_sphincs.signature.Reader.take 16#usize reader ⦃ out =>
      out = (some (RustParser.readPrefix 16#usize reader h), RustParser.readSuffix 16#usize reader) ⦄ := by
  rw [RustParser.take_success 16#usize reader h]
  simp only [WP.spec_ok]

@[step] theorem take_node_failure (reader : Slice U8) (h : reader.val.length < 16) :
    lean_sphincs.signature.Reader.take 16#usize reader ⦃ out => out = (none,reader) ⦄ := by
  rw [RustParser.take_failure 16#usize reader h]
  simp only [WP.spec_ok]

def parentBytes (address : Address) (node sibling : Node) (position : U32) : List U8 :=
  let right := (position &&& 1#u32) != 0#u32
  (address.val.setSlice! 48 (if right then sibling.val else node.val)).setSlice!
    64 (if right then node.val else sibling.val)

def halfPosition (position : U32) : U32 := ⟨position.bv >>> 1⟩

def parentStep (address : Address) (position : U32) (node sibling : Node) : Node × Address :=
  let preimage := parentBytes address node sibling position
  (Aeneas.Std.Array.from ((RustCrypto.digest preimage).val.take 16) (by simp),
   Aeneas.Std.Array.from preimage (by simp [preimage, parentBytes]))

@[step] theorem body_success (address : Address) (reader : Slice U8) (position : U32)
    (height level : U32) (node : Node) (hrun : level.val < height.val)
    (hread : 16 ≤ reader.val.length) :
    lean_sphincs.tree.climb_loop.body height address reader position node level ⦃ out =>
      match out with
      | .cont (nextAddress,nextReader,nextPosition,nextNode,nextLevel) =>
          nextLevel.val = level.val+1 ∧ nextPosition = halfPosition position ∧
          nextReader = RustParser.readSuffix 16#usize reader ∧
          (nextNode,nextAddress) = parentStep
            (positioned address (stepWord (level.val+1)) (halfPosition position)) position node
            (RustParser.readPrefix 16#usize reader hread)
      | .done _ => False ⦄ := by
  unfold lean_sphincs.tree.climb_loop.body
  have hbranch : level < height := by scalar_tac
  simp only [ite_eq_left hbranch]
  step
  step
  step
  step with take_node_success reader hread
  simp_all only [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  step*
  have hi : i = halfPosition position := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    exact i_post1
  have hl : level1 = stepWord (level.val+1) := by
    apply UScalar.eq_of_val_eq
    have hb : level.val+1 < 4294967296 := by scalar_tac
    change level1.val = (level.val+1) % 4294967296
    rw [Nat.mod_eq_of_lt hb]
    exact level1_post
  have hbit : i1 = position &&& 1#u32 := by scalar_tac
  have ha : address1 = positioned address (stepWord (level.val+1)) (halfPosition position) := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned, Aeneas.Std.Array.from_val, hi, hl] using address1_post
  refine ⟨level1_post, hi, ?_⟩
  apply Prod.ext
  · apply Aeneas.Std.Array.ext
    simpa only [parentStep, parentBytes, Aeneas.Std.Array.from_val, ha, hbit] using node1_post
  · apply Aeneas.Std.Array.ext
    simpa only [parentStep, parentBytes, Aeneas.Std.Array.from_val, ha, hbit] using node1_post1

@[step] theorem body_failure (address : Address) (reader : Slice U8) (position : U32)
    (height level : U32) (node : Node) (hrun : level.val < height.val)
    (hread : reader.val.length < 16) :
    lean_sphincs.tree.climb_loop.body height address reader position node level ⦃ out =>
      out = .done (none,
        positioned address (stepWord (level.val+1)) (halfPosition position), reader) ⦄ := by
  unfold lean_sphincs.tree.climb_loop.body
  have hbranch : level < height := by scalar_tac
  simp only [ite_eq_left hbranch]
  step
  step
  step
  step with take_node_failure reader hread
  simp_all only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  step*
  have hi : i = halfPosition position := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    exact i_post1
  have hl : level1 = stepWord (level.val+1) := by
    apply UScalar.eq_of_val_eq
    have hb : level.val+1 < 4294967296 := by scalar_tac
    change level1.val = (level.val+1) % 4294967296
    rw [Nat.mod_eq_of_lt hb]
    exact level1_post
  congr 3
  apply Aeneas.Std.Array.ext
  simpa only [positioned, Aeneas.Std.Array.from_val, hi, hl] using address1_post

def recover : Nat → Nat → Address → Slice U8 → U32 → Node → Option Node × Address × Slice U8
  | 0, _, address, reader, _, node => (some node,address,reader)
  | fuel+1, level, address, reader, position, node =>
      let nextAddress := positioned address (stepWord (level+1)) (halfPosition position)
      if hread : 16 ≤ reader.val.length then
        let next := parentStep nextAddress position node (RustParser.readPrefix 16#usize reader hread)
        recover fuel (level+1) next.2 (RustParser.readSuffix 16#usize reader)
          (halfPosition position) next.1
      else (none,nextAddress,reader)

/-- Complete source Merkle recovery, including every truncated-input branch and final state. -/
@[step] theorem loop_spec (address : Address) (reader : Slice U8) (position : U32)
    (height level : U32) (node : Node) :
    lean_sphincs.tree.climb_loop address reader position height node level ⦃ out =>
      out = recover (height.val-level.val) level.val address reader position node ⦄ := by
  let expected := recover (height.val-level.val) level.val address reader position node
  unfold lean_sphincs.tree.climb_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × U32 × Node × U32 => height.val-state.2.2.2.2.val)
    (fun state : Address × Slice U8 × U32 × Node × U32 =>
      expected = recover (height.val-state.2.2.2.2.val) state.2.2.2.2.val
        state.1 state.2.1 state.2.2.1 state.2.2.2.1)
  · rintro ⟨currentAddress,currentReader,currentPosition,currentNode,currentLevel⟩ hmodel
    dsimp only at hmodel
    dsimp only
    by_cases hrun : currentLevel.val < height.val
    · have hf : height.val-currentLevel.val = (height.val-(currentLevel.val+1))+1 := by omega
      by_cases hread : 16 ≤ currentReader.val.length
      · apply WP.spec_mono (body_success currentAddress currentReader currentPosition height currentLevel currentNode hrun hread)
        intro result hresult
        cases result with
        | done value => exact False.elim hresult
        | cont state =>
          rcases state with ⟨nextAddress,nextReader,nextPosition,nextNode,nextLevel⟩
          rcases hresult with ⟨hl,hp,hr,hn⟩
          refine ⟨?_, by scalar_tac⟩
          rw [hmodel, hf, recover, dite_eq_left hread]
          have ha := congrArg Prod.snd hn
          have hv := congrArg Prod.fst hn
          dsimp only at ha hv
          simp only [hl, hp, hr, ha, hv]
      · apply WP.spec_mono (body_failure currentAddress currentReader currentPosition height currentLevel currentNode hrun (by omega))
        intro result hresult
        subst result
        dsimp only
        change _ = expected
        rw [hmodel, hf, recover, dite_eq_right hread]
    · have hstop : ¬ currentLevel < height := by scalar_tac
      have hz : height.val-currentLevel.val = 0 := by omega
      simp only [lean_sphincs.tree.climb_loop.body, ite_eq_right hstop, WP.spec_ok]
      simpa only [hz, recover] using hmodel.symm
  · rfl

@[step] theorem climb_spec (address : Address) (reader : Slice U8) (position height : U32)
    (node : Node) :
    lean_sphincs.tree.climb address reader position height node ⦃ out =>
      out = recover height.val 0 address reader position node ⦄ := by
  unfold lean_sphincs.tree.climb
  step with loop_spec
  simp_all

end RustCrypto.Climb
