module
public import RustCrypto.ForsBatchFull
public import RustCrypto.ForsDigestBridge
public import RustCrypto.AppendNodes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

abbrev width := 2

@[step] theorem clone_spec (address : Address) :
    lean_sphincs.hash.HashContext.Insts.CoreCloneClone.clone address ⦃ out => out = address ⦄ := by
  unfold lean_sphincs.hash.HashContext.Insts.CoreCloneClone.clone
  step*

@[step] theorem clone_closure_spec (address : Address) (lane : Usize) :
    lean_sphincs.fors.recover_trees.closure.Insts.CoreOpsFunctionFnMutTupleUsizeHashContext.call_mut address lane
      ⦃ out => out.1 = address ∧ out.2 = address ⦄ := by
  unfold lean_sphincs.fors.recover_trees.closure.Insts.CoreOpsFunctionFnMutTupleUsizeHashContext.call_mut
  step*

@[step] theorem clone_array_spec (address : Address) :
    core.array.from_fn 2#usize
      lean_sphincs.fors.recover_trees.closure.Insts.CoreOpsFunctionFnMutTupleUsizeHashContext address
      ⦃ out => ∀ j < width, out[j]! = address ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _ (fun _ (value : Address) => value = address)
  intro lane hlane
  exact clone_closure_spec address lane

@[step] theorem position_closure_spec (digest : Aeneas.Std.Array U8 34#usize) (start lane : Usize)
    (hstart : start.val+width ≤ 24) (hlane : lane.val < width) :
    lean_sphincs.fors.recover_trees.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut (digest,start) lane
      ⦃ out => out.1.val = (start.val+lane.val)*1024 +
        EthLib.Cryptography.Sphincs.msbField (RustCrypto.ForsDigest.nativeDigest digest) (10*(start.val+lane.val)) 10 ∧
        out.2 = (digest,start) ⦄ := by
  unfold lean_sphincs.fors.recover_trees.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  step as ⟨position,hposition⟩
  step with RustCrypto.ForsDigest.leaf_position_ethlib_spec digest position (by omega) as ⟨value,hvalue⟩
  exact ⟨by simpa only [hposition] using hvalue,rfl⟩

@[step] theorem position_array_spec (digest : Aeneas.Std.Array U8 34#usize) (start : Usize)
    (hstart : start.val+width ≤ 24) :
    core.array.from_fn 2#usize
      lean_sphincs.fors.recover_trees.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 (digest,start)
      ⦃ out => ∀ j < width, (out[j]!).val = (start.val+j)*1024 +
        EthLib.Cryptography.Sphincs.msbField (RustCrypto.ForsDigest.nativeDigest digest) (10*(start.val+j)) 10 ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _ (fun j (value : U32) => value.val = (start.val+j)*1024 +
    EthLib.Cryptography.Sphincs.msbField (RustCrypto.ForsDigest.nativeDigest digest) (10*(start.val+j)) 10)
  intro lane hlane
  exact position_closure_spec digest start lane hstart hlane

end RustCrypto.ForsForest
