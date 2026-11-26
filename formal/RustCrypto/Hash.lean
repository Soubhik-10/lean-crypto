module
public import LeanSphincs.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto

/-- Both position words are written in network byte order; every other byte is retained. -/
@[step] theorem set_position_spec (self : lean_sphincs.hash.HashContext) (height position : U32) :
    lean_sphincs.hash.HashContext.set_position self height position ⦃ out =>
      out.val = self.val.take 40 ++ (core.num.U32.to_be_bytes height).val ++
        (core.num.U32.to_be_bytes position).val ++ self.val.drop 48 ⦄ := by
  unfold lean_sphincs.hash.HashContext.set_position
  step*
  have a_eq : a = core.num.U32.to_be_bytes height := by
    apply Aeneas.Std.Array.ext
    simpa [core.num.U32.to_be_bytes] using a_post
  have b_eq : a2 = core.num.U32.to_be_bytes position := by
    apply Aeneas.Std.Array.ext
    simpa [core.num.U32.to_be_bytes] using a2_post
  simp_all [List.setSlice!, List.append_assoc, List.take_append, List.drop_append,
    List.take_of_length_le]

/-- Public key seed initialization clears all address and payload fields. -/
@[step] theorem context_new_spec (public_key : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    lean_sphincs.hash.HashContext.new public_key ⦃ out =>
      out.val = public_key.val.take 16 ++ List.replicate 64 0#u8 ⦄ := by
  unfold lean_sphincs.hash.HashContext.new
  simp only [alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndex.index,
    lean_sphincs.core.ops.index.IndexArray, Aeneas.Std.core.ops.index.IndexArray,
    lean_sphincs.params.NODE_BYTES]
  step*
  simp_all [List.slice, List.setSlice!]

/-- Hash truncation retains exactly the first 128 bits. -/
@[step] theorem truncate_spec (input : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes 32#usize) :
    lean_sphincs.hash.truncate input ⦃ out => out.val = input.val.take 16 ⦄ := by
  unfold lean_sphincs.hash.truncate
  simp only [alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndex.index,
    lean_sphincs.core.ops.index.IndexArray, Aeneas.Std.core.ops.index.IndexArray,
    lean_sphincs.params.NODE_BYTES, alloy_primitives.bits.fixed.FixedBytes.new]
  step*
  simp_all [List.slice]

/-- Updating a tree retains the unused high 32 tree bits and every other field. -/
@[step] theorem set_tree_spec (self : lean_sphincs.hash.HashContext) (layer : U32) (tree : U64) :
    lean_sphincs.hash.HashContext.set_tree self layer tree ⦃ out =>
      out.val = (self.val.setSlice! 16 (core.num.U32.to_be_bytes layer).val).setSlice!
        24 (core.num.U64.to_be_bytes tree).val ⦄ := by
  unfold lean_sphincs.hash.HashContext.set_tree
  step*
  simp_all [core.num.U32.to_be_bytes, core.num.U64.to_be_bytes]

/-- Domain changes clear both position words and retain the seed/tree prefix. -/
@[step] theorem set_domain_spec (self : lean_sphincs.hash.HashContext) (domain pair : U32) :
    lean_sphincs.hash.HashContext.set_domain self domain pair ⦃ out =>
      out.val = ((self.val.setSlice! 32 (core.num.U32.to_be_bytes domain).val).setSlice!
        36 (core.num.U32.to_be_bytes pair).val).setSlice! 40 (List.replicate 8 0#u8) ⦄ := by
  unfold lean_sphincs.hash.HashContext.set_domain
  simp only [lean_sphincs.hash.PREFIX_BYTES]
  step*
  simp_all [core.num.U32.to_be_bytes]

/-- Incremental compression begins with exactly PK.seed and the 32-byte address. -/
@[step] theorem accumulator_spec (self : lean_sphincs.hash.HashContext) :
    lean_sphincs.hash.HashContext.accumulator self ⦃ out => out = self.val.take 48 ⦄ := by
  unfold lean_sphincs.hash.HashContext.accumulator
  simp only [alloy_primitives.utils.Keccak256.new, alloy_primitives.utils.Keccak256.update,
    Shared0T.Insts.CoreConvertAsRef.as_ref,
    Slice.Insts.CoreConvertAsRefSlice.as_ref, lean_sphincs.hash.PREFIX_BYTES]
  step*
  simp_all [List.slice]

end RustCrypto
