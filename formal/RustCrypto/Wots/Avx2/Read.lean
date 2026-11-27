module
public import RustCrypto.Wots.Recovery.Model
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem nodeList_get (bytes : List U8) (count offset i : Nat) (hi : i < count) :
    (nodeList bytes count offset)[i]'(by simpa only [nodeList_length] using hi) = ForsRead.nodeAt bytes (offset+16*i) := by
  induction count generalizing offset i with
  | zero => omega
  | succ count ih =>
    cases i with
    | zero => simp only [nodeList,List.getElem_cons_zero,Nat.mul_zero,Nat.add_zero]
    | succ i =>
      simp only [nodeList,List.getElem_cons_succ,ih (offset+16) i (by omega)]
      congr 1
      omega

def windowNodes (bytes : List U8) : Aeneas.Std.Array Node 16#usize :=
  Aeneas.Std.Array.from (nodeList bytes 16 0) (by simp)

theorem window_get (bytes : List U8) (i : Nat) (hi : i < 16) :
    (windowNodes bytes)[i]! = ForsRead.nodeAt bytes (16*i) := by
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos _ i (by simp only [windowNodes,Aeneas.Std.Array.from_val,nodeList_length]; exact hi)]
  simp only [windowNodes,Aeneas.Std.Array.from_val,nodeList_get bytes 16 0 i hi,Nat.zero_add]

@[step] theorem copy_closure_spec (input : Aeneas.Std.Array Node 16#usize) (index : Usize) (hindex : index.val < 16) :
    lean_sphincs.wots.read_window.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut input index
      ⦃ out => out.1 = input[index.val]! ∧ out.2 = input ⦄ := by
  unfold lean_sphincs.wots.read_window.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
  step as ⟨value,hvalue⟩
  simp only [alloy_primitives.bits.fixed.FixedBytes.new,bind_ok,WP.spec_ok]
  refine ⟨?_,True.intro⟩
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos input.val index.val (by scalar_tac)]
  exact hvalue

@[step] theorem copy_array_spec (input : Aeneas.Std.Array Node 16#usize) :
    core.array.from_fn 16#usize
      lean_sphincs.wots.read_window.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16 input
      ⦃ out => ∀ j < 16, out[j]! = input[j]! ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! _ _ _ (fun j (value : Node) => value = input[j]!)
  intro index hindex
  exact copy_closure_spec input index hindex

@[step] theorem first_window_spec (block : Aeneas.Std.Array U8 256#usize) :
    core.slice.Slice.first_chunk 16#usize (RustCrypto.chunks 16#usize (Aeneas.Std.Array.to_slice block))
      ⦃ out => ∃ values : Aeneas.Std.Array Node 16#usize,
        out = some values ∧ ∀ j < 16, (values[j]!).val = (block.val.drop (16*j)).take 16 ⦄ := by
  have hlen : (RustCrypto.chunks 16#usize (Aeneas.Std.Array.to_slice block)).val.length = 16 := by
    simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice]
  have hbound : (16#usize).val ≤ (RustCrypto.chunks 16#usize (Aeneas.Std.Array.to_slice block)).val.length := by
    change 16 ≤ _
    omega
  simp only [core.slice.Slice.first_chunk,dite_eq_left hbound,WP.spec_ok]
  refine ⟨_,rfl,?_⟩
  intro j hj
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos _ j (by scalar_tac)]
  simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,List.getElem_take,RustCrypto.chunks,Slice.from_val,
    List.getElem_ofFn,RustCrypto.chunk,Aeneas.Std.Array.to_slice]
  change (block.val.drop (j*16)).take 16 = (block.val.drop (16*j)).take 16
  rw [Nat.mul_comm j 16]

end RustCrypto.WotsAvx2
