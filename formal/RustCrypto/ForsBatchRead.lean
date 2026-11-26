module
public import RustCrypto.BatchPositions
public import RustCrypto.BatchParents
public import RustCrypto.ForsClimb
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def openingNode (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) : List U8 :=
  (opening.val.drop (16*level)).take 16

theorem chunk_at (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) (hlevel : level < 11) :
    ((RustCrypto.chunks 16#usize (Aeneas.Std.Array.to_slice opening)).val[level]!).val = openingNode opening level := by
  have hlen : (RustCrypto.chunks 16#usize (Aeneas.Std.Array.to_slice opening)).val.length = 11 := by
    simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice]
  rw [getElem!_pos _ level (by omega)]
  simp only [RustCrypto.chunks,Slice.from_val,List.getElem_ofFn,RustCrypto.chunk,Aeneas.Std.Array.from_val,
    Aeneas.Std.Array.to_slice,openingNode]
  change (opening.val.drop (level*16)).take 16 = (opening.val.drop (16*level)).take 16
  rw [Nat.mul_comm level 16]

@[step] theorem sibling_closure_spec (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (level : U32) (hlevel : level.val < 11) (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.fors.recover_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
      (openings,level) lane ⦃ out => out.1.val = openingNode (openings[lane.val]!) level.val ∧ out.2 = (openings,level) ⦄ := by
  unfold lean_sphincs.fors.recover_batch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
  step as ⟨current,hcurrent⟩
  have hc : current = openings[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos openings.val lane.val (by scalar_tac)]
    exact hcurrent
  rw [hc]
  step as ⟨slice,hslice⟩
  rw [hslice]
  simp only [core.slice.Slice.as_chunks]
  have hn : ¬(16#usize).val = 0 := by decide
  simp only [ite_eq_right hn]
  step as ⟨offset,hoffset⟩
  step as ⟨node,hnode⟩ by simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice]; scalar_tac
  simp only [alloy_primitives.bits.fixed.FixedBytes.new,bind_ok,WP.spec_ok]
  change node.val = openingNode (openings[lane.val]!) level.val ∧ (openings,level) = (openings,level)
  constructor
  · have ho : offset.val = level.val := by scalar_tac
    rw [hnode,← getElem!_pos _ offset.val (by simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice]; omega),ho]
    exact chunk_at _ _ hlevel
  · rfl

@[step] theorem first_closure_spec (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.fors.recover_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
      openings lane ⦃ out => out.1.val = openingNode (openings[lane.val]!) 0 ∧ out.2 = openings ⦄ := by
  unfold lean_sphincs.fors.recover_batch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
  step as ⟨current,hcurrent⟩
  have hc : current = openings[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos openings.val lane.val (by scalar_tac)]
    exact hcurrent
  rw [hc]
  step as ⟨slice,hslice⟩
  rw [hslice]
  simp only [core.slice.Slice.as_chunks]
  have hn : ¬(16#usize).val = 0 := by decide
  simp only [ite_eq_right hn]
  step as ⟨node,hnode⟩ by simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice]
  simp only [alloy_primitives.bits.fixed.FixedBytes.new,bind_ok,WP.spec_ok]
  constructor
  · rw [hnode,← getElem!_pos _ 0 (by simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice])]
    exact chunk_at _ _ (by decide)
  · trivial

@[step] theorem parent_closure_spec (positions : Aeneas.Std.Array U32 2#usize)
    (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.fors.recover_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      positions lane ⦃ out => out.1 = RustCrypto.Climb.halfPosition (positions[lane.val]!) ∧ out.2 = positions ⦄ := by
  unfold lean_sphincs.fors.recover_batch.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  step as ⟨position,hposition⟩
  step as ⟨parent,hparent,hparentVal⟩
  have hp : position = positions[lane.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos positions.val lane.val (by scalar_tac)]
    exact hposition
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  simpa only [RustCrypto.Climb.halfPosition,hp] using hparentVal

end RustCrypto.ForsBatch
