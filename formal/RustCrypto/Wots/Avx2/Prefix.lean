module
public import RustCrypto.Wots.Recovery.Layout
public import RustCrypto.Fors.Forest.Prefix
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000

theorem ends_before_add (bytes : List U8) (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (start count : Nat) :
    WotsRecover.endsBefore bytes word seed key (start+count) = WotsRecover.endsBefore bytes word seed key start ++
      (((WotsRecover.endVector bytes word seed key).toList.drop start).take count).flatMap Vector.toList := by
  unfold WotsRecover.endsBefore OrderedPrefix.collect
  rw [List.take_add,List.flatMap_append]

@[step] theorem clone_closure_spec (address : Address) (lane : Usize) :
    lean_sphincs.wots.recover_chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeHashContext.call_mut address lane
      ⦃ out => out.1 = address ∧ out.2 = address ⦄ := by
  unfold lean_sphincs.wots.recover_chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeHashContext.call_mut
  step*

@[step] theorem clone_array_spec (address : Address) :
    core.array.from_fn 4#usize
      lean_sphincs.wots.recover_chains.closure.Insts.CoreOpsFunctionFnMutTupleUsizeHashContext address
      ⦃ out => ∀ j < 4, out[j]! = address ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _ (fun _ (value : Address) => value = address)
  intro lane hlane
  exact clone_closure_spec address lane

end RustCrypto.WotsAvx2
