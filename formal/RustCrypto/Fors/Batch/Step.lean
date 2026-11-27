module
public import RustCrypto.Fors.Batch.FromFn
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 100000
set_option maxRecDepth 8192

def nodeAt (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) (hlevel : level < 11) : Node :=
  Aeneas.Std.Array.from (openingNode opening level) (by
    change (openingNode opening level).length = 16
    simp only [openingNode,List.length_take,List.length_drop]
    have hl : opening.val.length = 176 := by scalar_tac
    rw [hl]
    omega)

@[simp] theorem nodeAt_val (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) (hlevel : level < 11) :
    (nodeAt opening level hlevel).val = openingNode opening level := by
  simp only [nodeAt,Aeneas.Std.Array.from_val]

@[step] theorem batch_body_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize) (nodes : Aeneas.Std.Array Node 2#usize)
    (level : U32) (hlevel : level.val < 10) :
    lean_sphincs.fors.recover_batch_loop.body openings addresses positions nodes level ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddresses,nextPositions,nextNodes,nextLevel) =>
          nextLevel.val = level.val+1 ∧ ∀ j < 2,
            nextPositions[j]! = RustCrypto.Climb.halfPosition (positions[j]!) ∧
            (nextNodes[j]!,nextAddresses[j]!) = RustCrypto.Climb.parentStep
              (positioned (addresses[j]!) (stepWord (level.val+1)) (RustCrypto.Climb.halfPosition (positions[j]!)))
              (positions[j]!) (nodes[j]!) (nodeAt (openings[j]!) (level.val+1) (by omega)) ⦄ := by
  unfold lean_sphincs.fors.recover_batch_loop.body
  have hrun : level < lean_sphincs.params.FORS_HEIGHT := by
    simp only [lean_sphincs.params.FORS_HEIGHT]
    scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨nextLevel,hnextLevel⟩
  step with parent_array_spec positions as ⟨parents,hparents⟩
  step with BatchPositions.set_positions_spec addresses nextLevel parents as ⟨positionedAddresses,hpositions⟩
  step with sibling_array_spec openings nextLevel (by scalar_tac) as ⟨siblings,hsiblings⟩
  step with BatchParents.hash_parents_spec positionedAddresses nodes siblings positions
    as ⟨nextNodes,nextAddresses,hnextNodes,hnextAddresses⟩
  refine ⟨hnextLevel,?_⟩
  intro j hj
  refine ⟨hparents j hj,?_⟩
  have hword : nextLevel = stepWord (level.val+1) := by
    apply UScalar.eq_of_val_eq
    change nextLevel.val = (level.val+1)%4294967296
    rw [Nat.mod_eq_of_lt (by scalar_tac)]
    exact hnextLevel
  have hpositioned : positionedAddresses[j]! = positioned (addresses[j]!) nextLevel (parents[j]!) := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned,Aeneas.Std.Array.from_val,BatchPositions.addressBytes] using hpositions j hj
  have hsibling : siblings[j]! = nodeAt (openings[j]!) (level.val+1) (by omega) := by
    apply Aeneas.Std.Array.ext
    simpa only [nodeAt_val,hnextLevel] using hsiblings j hj
  apply Prod.ext
  · apply Aeneas.Std.Array.ext
    simp only [RustCrypto.Climb.parentStep,Aeneas.Std.Array.from_val]
    rw [hnextNodes j hj,hpositioned,hword,hparents j hj,hsibling]
    rfl
  · apply Aeneas.Std.Array.ext
    simp only [RustCrypto.Climb.parentStep,Aeneas.Std.Array.from_val]
    rw [hnextAddresses j hj,hpositioned,hword,hparents j hj,hsibling]
    rfl

end RustCrypto.ForsBatch
