module
public import RustCrypto.ReadBytes
public import Mathlib.Tactic.FinCases
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ShortHash
set_option maxHeartbeats 2000000

@[step] theorem chunks_eight_spec (input : Slice U8) :
    core.slice.Slice.as_chunks 8#usize input ⦃ out =>
      out.1.val = List.ofFn (RustCrypto.chunk 8#usize input) ⦄ := by
  simp [core.slice.Slice.as_chunks, RustCrypto.chunks, WP.spec_ok]

@[step] theorem decode_word_spec (input : Aeneas.Std.Array U8 8#usize) :
    lift (core.num.U64.from_le_bytes input) ⦃ out =>
      ByteBridge.word out =
        EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes input.val) 0 ⦄ := by
  simp only [lift, WP.spec_ok]
  exact ByteBridge.decode_eight input

/-- The source nested closure reads the correct independent input and little-endian word. -/
@[step] theorem load_call_spec {n : Usize} (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 n) 2#usize)
    (index lane : Usize) (hindex : index.val < n.val/8) (hlane : lane.val < 2) :
    lean_sphincs.hash.batch.hash.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (inputs,index) lane ⦃ out =>
        ByteBridge.word out.1 = EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs[lane.val]!).val) (8*index.val) ∧
        out.2 = (inputs,index) ⦄ := by
  unfold lean_sphincs.hash.batch.hash.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step*
  · simp_all [Slice.length]
  · constructor
    · rw [i1_post]
      have harray : a2.val = (((inputs.val[lane.val]'(by simpa using hlane)).val).drop
          (index.val*8)).take 8 := by
        simp_all [RustCrypto.chunk, Aeneas.Std.Array.from_val, List.getElem_ofFn]
      rw [harray]
      have hm := Nat.mul_le_mul_right 8 (show index.val+1 ≤ n.val/8 by omega)
      have hcap := Nat.div_mul_le_self n.val 8
      have hroom : index.val*8+8 ≤ (inputs.val[lane.val]'(by simpa using hlane)).val.length := by
        have hlen : (inputs.val[lane.val]'(by simpa using hlane)).val.length = n.val :=
          (inputs.val[lane.val]'(by simpa using hlane)).property
        omega
      have hread := ByteBridge.laneAt_slice
        (inputs.val[lane.val]'(by simpa using hlane)).val (index.val*8) hroom
      simpa only [Aeneas.Std.Array.getElem!_Nat_eq,
        getElem!_pos inputs.val lane.val (by simpa using hlane), Nat.mul_comm] using hread
    · rfl


@[step] theorem load_array_spec {n : Usize}
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 n) 2#usize) (index : Usize)
    (hindex : index.val < n.val/8) :
    core.array.from_fn 2#usize
      (lean_sphincs.hash.batch.hash.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 n)
      (inputs,index) ⦃ out => ∀ lane < 2,
        ByteBridge.word (out[lane]!) = EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs[lane]!).val) (8*index.val) ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! 2#usize
    (lean_sphincs.hash.batch.hash.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 n)
    (inputs,index) (fun lane value => ByteBridge.word value =
      EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane]!).val)
        (8*index.val))
  intro lane hlane
  exact load_call_spec inputs index lane hindex (by simpa using hlane)

@[step] theorem wide_new_spec (values : Aeneas.Std.Array U64 2#usize) :
    wide.u64x2_.u64x2.new values ⦃ out => out = fun lane => values[lane.val]! ⦄ := by
  simp only [wide.u64x2_.u64x2.new, WP.spec_ok]
  funext lane
  rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos values.val lane.val (by
    have hi := lane.isLt
    scalar_tac)]

@[step] theorem initial_call_spec {n : Usize}
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 n) 2#usize) (index : Usize) :
    lean_sphincs.hash.batch.hash.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
      inputs index ⦃ out =>
        (∀ lane : Fin 2, ByteBridge.word (out.1 lane) =
          if index.val < n.val/8 then EthLib.Cryptography.Hash.Keccak.Internal.laneAt
            (RustCrypto.bytes (inputs[lane.val]!).val) (8*index.val) else 0) ∧
        out.2 = inputs ⦄ := by
  unfold lean_sphincs.hash.batch.hash.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
  step
  split
  · step*
  · step*
    intro lane
    fin_cases lane <;> simp_all [ByteBridge.word]

/-- Every initialized source state word contains the corresponding input word, or zero. -/
@[step] theorem initial_array_spec {n : Usize}
    (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 n) 2#usize) :
    core.array.from_fn 25#usize
      (lean_sphincs.hash.batch.hash.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2 n)
      inputs ⦃ out => ∀ i < 25, ∀ lane : Fin 2, ByteBridge.word (out[i]! lane) =
        if i < n.val/8 then EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs[lane.val]!).val) (8*i) else 0 ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! 25#usize
    (lean_sphincs.hash.batch.hash.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2 n)
    inputs (fun i value => ∀ lane : Fin 2, ByteBridge.word (value lane) =
      if i < n.val/8 then EthLib.Cryptography.Hash.Keccak.Internal.laneAt
        (RustCrypto.bytes (inputs[lane.val]!).val) (8*i) else 0)
  intro index _
  exact initial_call_spec inputs index

end RustCrypto.ShortHash
