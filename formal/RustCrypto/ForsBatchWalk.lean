module
public import RustCrypto.ForsBatchStep
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def readNode (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) : Node :=
  if hlevel : level < 11 then nodeAt opening level hlevel
  else Aeneas.Std.Array.from (List.replicate 16 0#u8) (by simp)

theorem readNode_eq (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) (hlevel : level < 11) :
    readNode opening level = nodeAt opening level hlevel := by
  simp only [readNode,dite_eq_left hlevel]

def walk (opening : Aeneas.Std.Array U8 176#usize) :
    (fuel level : Nat) → U32 → Node → Address → Node × Address
  | 0,_,_,node,address => (node,address)
  | fuel+1,level,position,node,address =>
      let parent := RustCrypto.Climb.halfPosition position
      let step := RustCrypto.Climb.parentStep (positioned address (stepWord (level+1)) parent)
        position node (readNode opening (level+1))
      walk opening fuel (level+1) parent step.1 step.2

@[step] theorem batch_loop_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize) (nodes : Aeneas.Std.Array Node 2#usize)
    (level : U32) (hlevel : level.val ≤ 10) :
    lean_sphincs.fors.recover_batch_loop addresses openings positions nodes level ⦃ out =>
      ∀ j < 2, (out.1[j]!,out.2[j]!) =
        walk (openings[j]!) (10-level.val) level.val (positions[j]!) (nodes[j]!) (addresses[j]!) ⦄ := by
  unfold lean_sphincs.fors.recover_batch_loop
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Address 2#usize × Aeneas.Std.Array U32 2#usize ×
      Aeneas.Std.Array Node 2#usize × U32 => 10-state.2.2.2.val)
    (fun state => state.2.2.2.val ≤ 10 ∧ ∀ j < 2,
      walk (openings[j]!) (10-state.2.2.2.val) state.2.2.2.val
        (state.2.1[j]!) (state.2.2.1[j]!) (state.1[j]!) =
      walk (openings[j]!) (10-level.val) level.val (positions[j]!) (nodes[j]!) (addresses[j]!))
  · rintro ⟨currentAddresses,currentPositions,currentNodes,currentLevel⟩ ⟨hbound,hcurrent⟩
    dsimp only at hbound hcurrent
    dsimp only
    by_cases hrun : currentLevel.val < 10
    · apply WP.spec_mono (batch_body_spec currentAddresses openings currentPositions currentNodes currentLevel hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddresses,nextPositions,nextNodes,nextLevel⟩
        rcases hresult with ⟨hnextLevel,hnext⟩
        dsimp only
        refine ⟨⟨by omega,?_⟩,by omega⟩
        intro j hj
        rcases hnext j hj with ⟨hparent,hstep⟩
        have hnode := congrArg Prod.fst hstep
        have haddress := congrArg Prod.snd hstep
        dsimp only at hnode haddress
        have hfuel : 10-currentLevel.val = (10-(currentLevel.val+1))+1 := by omega
        have hwalk : walk (openings[j]!) (10-currentLevel.val) currentLevel.val
            (currentPositions[j]!) (currentNodes[j]!) (currentAddresses[j]!) =
            walk (openings[j]!) (10-nextLevel.val) nextLevel.val
              (nextPositions[j]!) (nextNodes[j]!) (nextAddresses[j]!) := by
          rw [hfuel,walk]
          simp only [hnextLevel,hparent,hnode,haddress,readNode_eq _ _ (by omega : currentLevel.val+1 < 11)]
        exact hwalk.symm.trans (hcurrent j hj)
    · have hc : currentLevel.val = 10 := by omega
      have hstop : ¬currentLevel < lean_sphincs.params.FORS_HEIGHT := by
        simp only [lean_sphincs.params.FORS_HEIGHT]
        scalar_tac
      simp only [lean_sphincs.fors.recover_batch_loop.body,ite_eq_right hstop,WP.spec_ok]
      intro j hj
      simpa only [hc,Nat.sub_self,walk] using hcurrent j hj
  · exact ⟨hlevel,by intro j hj; rfl⟩

end RustCrypto.ForsBatch
