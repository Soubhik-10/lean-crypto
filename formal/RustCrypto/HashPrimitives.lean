module
public import RustCrypto.Hash
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto
set_option maxHeartbeats 2000000

@[step] theorem first_chunk_spec (n : Usize) (bytes : Slice U8)
    (h : n.val ≤ bytes.val.length) :
    core.slice.Slice.first_chunk n bytes ⦃ out => out = some (RustParser.readPrefix n bytes h) ⦄ := by
  simp [core.slice.Slice.first_chunk, h, WP.spec_ok]

@[step] theorem node_input_spec (self : lean_sphincs.hash.HashContext)
    (value : Aeneas.Std.Array U8 16#usize) :
    lean_sphincs.hash.HashContext.node_input self value ⦃ out =>
      out.1.val = self.val.take 48 ++ value.val ∧
      out.2.val = self.val.setSlice! 48 value.val ⦄ := by
  unfold lean_sphincs.hash.HashContext.node_input
  simp only [lean_sphincs.hash.NODE_INPUT_BYTES, lean_sphincs.hash.PREFIX_BYTES,
    lean_sphincs.params.NODE_BYTES]
  step*
  simp_all [core.option.Option.expect, WP.spec_ok, RustParser.readPrefix,
    List.setSlice!, List.take_append, List.take_of_length_le]

@[step] theorem parent_input_spec (self : lean_sphincs.hash.HashContext)
    (value sibling : Aeneas.Std.Array U8 16#usize) (right : Bool) :
    lean_sphincs.hash.HashContext.parent_input self value sibling right ⦃ out =>
      out.1 = out.2 ∧ out.1.val =
        (self.val.setSlice! 48 (if right then sibling.val else value.val)).setSlice!
          64 (if right then value.val else sibling.val) ⦄ := by
  cases right <;>
    (unfold lean_sphincs.hash.HashContext.parent_input
     simp only [lean_sphincs.hash.NODE_INPUT_BYTES, lean_sphincs.hash.PREFIX_BYTES,
       lean_sphincs.params.NODE_BYTES]
     simp_all
     step*)

@[step] theorem derive_secret_spec (self : lean_sphincs.hash.HashContext)
    (seed : Aeneas.Std.Array U8 32#usize) :
    lean_sphincs.hash.HashContext.derive_secret self seed ⦃ out =>
      let input := self.val.setSlice! 48 seed.val
      out.1.val = (RustCrypto.digest input).val.take 16 ∧ out.2.val = input ⦄ := by
  unfold lean_sphincs.hash.HashContext.derive_secret
  simp only [lean_sphincs.hash.PREFIX_BYTES,
    alloy_primitives.bits.fixed.FixedBytes.as_slice,
    alloy_primitives.utils.keccak256_uncached,
    Aeneas.Std.Array.Insts.CoreConvertAsRefSlice.as_ref]
  step*

@[step] theorem hash_node_spec (self : lean_sphincs.hash.HashContext)
    (value : Aeneas.Std.Array U8 16#usize) :
    lean_sphincs.hash.HashContext.hash_node self value ⦃ out =>
      out.1.val = (digest (self.val.take 48 ++ value.val)).val.take 16 ∧
      out.2.val = self.val.setSlice! 48 value.val ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_node
  simp only [alloy_primitives.utils.keccak256_uncached,
    Shared0T.Insts.CoreConvertAsRef.as_ref,
    Aeneas.Std.Array.Insts.CoreConvertAsRefSlice.as_ref]
  step*

@[step] theorem hash_parent_spec (self : lean_sphincs.hash.HashContext)
    (value sibling : Aeneas.Std.Array U8 16#usize) (right : Bool) :
    lean_sphincs.hash.HashContext.hash_parent self value sibling right ⦃ out =>
      let input := (self.val.setSlice! 48 (if right then sibling.val else value.val)).setSlice!
        64 (if right then value.val else sibling.val)
      out.1.val = (digest input).val.take 16 ∧ out.2.val = input ⦄ := by
  unfold lean_sphincs.hash.HashContext.hash_parent
  simp only [alloy_primitives.utils.keccak256_uncached,
    Shared0T.Insts.CoreConvertAsRef.as_ref,
    Aeneas.Std.Array.Insts.CoreConvertAsRefSlice.as_ref]
  step*

@[step] theorem encode_spec (self : lean_sphincs.hash.HashContext)
    (message : Aeneas.Std.Array U8 16#usize) (counter : Aeneas.Std.Array U8 4#usize) :
    lean_sphincs.hash.HashContext.encode self message counter ⦃ out =>
      let input := (self.val.setSlice! 48 message.val).setSlice! 64 counter.val
      out.1.val = (digest (input.take 68)).val.take 16 ∧ out.2.val = input ⦄ := by
  unfold lean_sphincs.hash.HashContext.encode
  simp only [lean_sphincs.hash.HashContext.encode.ENCODE_INPUT_BYTES,
    lean_sphincs.hash.NODE_INPUT_BYTES, lean_sphincs.hash.PREFIX_BYTES,
    lean_sphincs.params.NODE_BYTES, alloy_primitives.bits.fixed.FixedBytes.as_slice,
    alloy_primitives.utils.keccak256_uncached,
    Shared0T.Insts.CoreConvertAsRef.as_ref, Slice.Insts.CoreConvertAsRefSlice.as_ref]
  step*
  simp_all [List.slice]

@[step] theorem message_digest_spec (public_key message : Aeneas.Std.Array U8 32#usize)
    (randomizer : Aeneas.Std.Array U8 16#usize) :
    lean_sphincs.hash.message_digest public_key message randomizer ⦃ out =>
      let input := randomizer.val ++ public_key.val ++ message.val
      out.val = (digest (input ++ [0#u8, 0#u8, 0#u8, 0#u8])).val ++
        (digest (input ++ [0#u8, 0#u8, 0#u8, 1#u8])).val.take 2 ⦄ := by
  unfold lean_sphincs.hash.message_digest
  simp only [alloy_primitives.bits.fixed.FixedBytes.as_slice,
    alloy_primitives.utils.keccak256_uncached,
    Aeneas.Std.Array.Insts.CoreConvertAsRefSlice.as_ref,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndex.index,
    lean_sphincs.core.ops.index.IndexArray, Aeneas.Std.core.ops.index.IndexArray]
  step*
  all_goals simp_all [List.slice, List.setSlice!, List.take_append, List.drop_append,
    List.append_assoc, List.take_of_length_le, List.drop_of_length_le]

end RustCrypto
