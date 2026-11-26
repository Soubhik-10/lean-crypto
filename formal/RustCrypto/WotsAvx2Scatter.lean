module
public import RustCrypto.WotsRecoverModel
public import RustCrypto.BatchNodes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def scatter (chains : Aeneas.Std.Array Usize 4#usize) (values : Aeneas.Std.Array Node 4#usize) :
    Nat → Nat → Aeneas.Std.Array Node 16#usize → Aeneas.Std.Array Node 16#usize
  | 0,_,nodes => nodes
  | fuel+1,lane,nodes => scatter chains values fuel (lane+1) (nodes.set (chains[lane]!) (values[lane]!))

@[step] theorem scatter_body_spec (nodes : Aeneas.Std.Array Node 16#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (values : Aeneas.Std.Array Node 4#usize) (lane : Usize)
    (hlane : lane.val < 4) (hchains : ∀ j < 4, (chains[j]!).val < 16) :
    lean_sphincs.wots.recover_group_loop1.body chains values nodes lane ⦃ out =>
      match out with
      | .done _ => False
      | .cont (next,nextLane) => nextLane.val = lane.val+1 ∧ next = nodes.set (chains[lane.val]!) (values[lane.val]!) ⦄ := by
  unfold lean_sphincs.wots.recover_group_loop1.body
  have hrun : lane < lean_sphincs.hash.batch.WIDTH := by
    simp only [lean_sphincs.hash.batch.WIDTH]
    scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨value,hvalue⟩
  step as ⟨index,hindex⟩
  have hi : index = chains[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos chains.val lane.val (by scalar_tac)]
    exact hindex
  have hbound : index.val < 16 := by rw [hi]; exact hchains lane.val hlane
  step as ⟨next,hnext⟩
  step as ⟨nextLane,hnextLane⟩
  have hv : value = values[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos values.val lane.val (by scalar_tac)]
    exact hvalue
  refine ⟨hnextLane,?_⟩
  simpa only [hi,hv] using hnext

@[step] theorem scatter_loop_spec (nodes : Aeneas.Std.Array Node 16#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (values : Aeneas.Std.Array Node 4#usize) (lane : Usize)
    (hlane : lane.val ≤ 4) (hchains : ∀ j < 4, (chains[j]!).val < 16) :
    lean_sphincs.wots.recover_group_loop1 nodes chains values lane ⦃ out => out = scatter chains values (4-lane.val) lane.val nodes ⦄ := by
  let expected := scatter chains values (4-lane.val) lane.val nodes
  unfold lean_sphincs.wots.recover_group_loop1
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array Node 16#usize × Usize => 4-state.2.val)
    (fun state => state.2.val ≤ 4 ∧ expected = scatter chains values (4-state.2.val) state.2.val state.1)
  · rintro ⟨current,currentLane⟩ ⟨hbound,hmodel⟩
    dsimp only at hbound hmodel
    dsimp only
    by_cases hrun : currentLane.val < 4
    · apply WP.spec_mono (scatter_body_spec current chains values currentLane hrun hchains)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨next,nextLane⟩
        rcases hresult with ⟨hnextLane,hnext⟩
        dsimp only
        refine ⟨⟨by omega,?_⟩,by omega⟩
        have hfuel : 4-currentLane.val = (4-(currentLane.val+1))+1 := by omega
        rw [hnextLane,hnext]
        rw [hfuel,scatter] at hmodel
        exact hmodel
    · have hc : currentLane.val = 4 := by omega
      have hstop : ¬currentLane < lean_sphincs.hash.batch.WIDTH := by
        simp only [lean_sphincs.hash.batch.WIDTH]
        scalar_tac
      simp only [lean_sphincs.wots.recover_group_loop1.body,ite_eq_right hstop,WP.spec_ok]
      simpa only [hc,Nat.sub_self,scatter] using hmodel.symm
  · exact ⟨hlane,rfl⟩

end RustCrypto.WotsAvx2
