module
public import RustCrypto.Fors.Batch.Read
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

@[step] theorem sibling_array_spec (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (level : U32) (hlevel : level.val < 11) :
    core.array.from_fn 2#usize
      lean_sphincs.fors.recover_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16 (openings,level)
      ⦃ out => ∀ j < 2, (out[j]!).val = openingNode (openings[j]!) level.val ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _
    (fun j (value : Node) => value.val = openingNode (openings[j]!) level.val)
  intro lane hlane
  exact sibling_closure_spec openings level hlevel lane hlane

@[step] theorem first_array_spec (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize) :
    core.array.from_fn 2#usize
      lean_sphincs.fors.recover_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16 openings
      ⦃ out => ∀ j < 2, (out[j]!).val = openingNode (openings[j]!) 0 ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _
    (fun j (value : Node) => value.val = openingNode (openings[j]!) 0)
  intro lane hlane
  exact first_closure_spec openings lane hlane

@[step] theorem parent_array_spec (positions : Aeneas.Std.Array U32 2#usize) :
    core.array.from_fn 2#usize
      lean_sphincs.fors.recover_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 positions
      ⦃ out => ∀ j < 2, out[j]! = RustCrypto.Climb.halfPosition (positions[j]!) ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _
    (fun j (value : U32) => value = RustCrypto.Climb.halfPosition (positions[j]!))
  intro lane hlane
  exact parent_closure_spec positions lane hlane

end RustCrypto.ForsBatch
