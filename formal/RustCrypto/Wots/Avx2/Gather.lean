module
public import RustCrypto.Wots.Recovery.Model
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

@[step] theorem gather_closure_spec (nodes : Aeneas.Std.Array Node 16#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (lane : Usize) (hlane : lane.val < 4)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) :
    lean_sphincs.wots.recover_group.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut (nodes,chains) lane
      ⦃ out => out.1 = nodes[(chains[lane.val]!).val]! ∧ out.2 = (nodes,chains) ⦄ := by
  unfold lean_sphincs.wots.recover_group.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
  step as ⟨selected,hselected⟩
  have hs : selected = chains[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos chains.val lane.val (by scalar_tac)]
    exact hselected
  have hb : selected.val < 16 := by rw [hs]; exact hchains lane.val hlane
  step as ⟨value,hvalue⟩
  refine ⟨?_,rfl⟩
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos nodes.val (chains[lane.val]!).val (by scalar_tac)]
  simpa only [hs] using hvalue

@[step] theorem gather_array_spec (nodes : Aeneas.Std.Array Node 16#usize)
    (chains : Aeneas.Std.Array Usize 4#usize) (hchains : ∀ j < 4, (chains[j]!).val < 16) :
    core.array.from_fn 4#usize
      lean_sphincs.wots.recover_group.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16 (nodes,chains)
      ⦃ out => ∀ j < 4, out[j]! = nodes[(chains[j]!).val]! ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _ (fun j (value : Node) => value = nodes[(chains[j]!).val]!)
  intro lane hlane
  exact gather_closure_spec nodes chains lane hlane hchains

end RustCrypto.WotsAvx2
