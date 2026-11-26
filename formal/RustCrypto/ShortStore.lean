module
public import RustCrypto.ReadBytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ShortHash
set_option maxHeartbeats 2000000

@[step] theorem to_le_value_spec (input : U64) :
    lift (core.num.U64.to_le_bytes input) ⦃ out => out = core.num.U64.to_le_bytes input ⦄ := by
  simp [lift, WP.spec_ok]

/-- The actual output closure serializes the low and high words in little-endian order. -/
@[step] theorem output_call_spec {n : Usize} (low high : Aeneas.Std.Array U64 2#usize)
    (lane : Usize) (hlane : lane.val < 2) :
    lean_sphincs.hash.batch.hash.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
      (N := n) (low,high) lane ⦃ out =>
        out.1.val = (core.num.U64.to_le_bytes (low[lane.val]!)).val ++
          (core.num.U64.to_le_bytes (high[lane.val]!)).val ∧
        out.2 = (low,high) ⦄ := by
  unfold lean_sphincs.hash.batch.hash.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
  simp only [alloy_primitives.bits.fixed.FixedBytes.new]
  step*
  simp_all [List.setSlice!, List.drop_append, List.append_assoc,
    List.take_of_length_le, Aeneas.Std.Array.getElem!_Nat_eq]
  rfl

@[step] theorem output_array_spec {n : Usize} (low high : Aeneas.Std.Array U64 2#usize) :
    core.array.from_fn 2#usize
      (lean_sphincs.hash.batch.hash.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16 n)
      (low,high) ⦃ out => ∀ lane < 2,
        (out[lane]!).val = (core.num.U64.to_le_bytes (low[lane]!)).val ++
          (core.num.U64.to_le_bytes (high[lane]!)).val ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! 2#usize
    (lean_sphincs.hash.batch.hash.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16 n)
    (low,high) (fun lane value => value.val =
      (core.num.U64.to_le_bytes (low[lane]!)).val ++
        (core.num.U64.to_le_bytes (high[lane]!)).val)
  intro lane hlane
  exact output_call_spec low high lane (by simpa using hlane)

end RustCrypto.ShortHash
