module
public import RustCrypto.HashPrimitives
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.SigningBytes
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def seedTag : List U8 := [108#u8,101#u8,97#u8,110#u8,83#u8,80#u8,72#u8,73#u8,78#u8,67#u8,83#u8]

@[simp] theorem seed_tag_spec : lean_sphincs.params.SEED_TAG.val = seedTag := by
  simp [lean_sphincs.params.SEED_TAG, seedTag]

@[simp] theorem tag_length_cast (tag : Aeneas.Std.Array U8 11#usize) :
    UScalar.cast .U8 tag.to_slice.len = 11#u8 := by
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast_val_eq]

/-- Both source key-expansion hashes have exactly their specified, distinct suffix bytes. -/
@[step] theorem expand_key_spec (seed : Aeneas.Std.Array U8 32#usize) :
    lean_sphincs.signing.expand_key seed ⦃ out =>
      out.1.val = (RustCrypto.digest (seedTag ++ seed.val ++ [0#u8])).val.take 16 ∧
      out.2 = RustCrypto.digest (seedTag ++ seed.val ++ [1#u8]) ⦄ := by
  unfold lean_sphincs.signing.expand_key
  simp only [lean_sphincs.params.SEED_TAG,
    alloy_primitives.bits.fixed.FixedBytes.as_slice,
    alloy_primitives.utils.keccak256_uncached,
    Aeneas.Std.Array.Insts.CoreConvertAsRefSlice.as_ref]
  step*
  simp_all [seedTag, List.setSlice!, List.take_of_length_le]

/-- The source randomizer binds SK.prf, PK.seed, the domain byte, tag length, tag and message. -/
@[step] theorem randomizer_spec (sk_prf message : Aeneas.Std.Array U8 32#usize)
    (pk_seed : Aeneas.Std.Array U8 16#usize) :
    lean_sphincs.signing.randomizer sk_prf pk_seed message ⦃ out =>
      out.val = (RustCrypto.digest (sk_prf.val ++ pk_seed.val ++ [0#u8,11#u8] ++
        seedTag ++ message.val)).val.take 16 ⦄ := by
  unfold lean_sphincs.signing.randomizer
  simp only [lean_sphincs.params.SEED_TAG,
    alloy_primitives.bits.fixed.FixedBytes.as_slice,
    alloy_primitives.utils.keccak256_uncached,
    Aeneas.Std.Array.Insts.CoreConvertAsRefSlice.as_ref]
  step*
  all_goals simp_all [seedTag, List.setSlice!, List.take_append, List.drop_append,
    List.append_assoc, List.take_of_length_le]

end RustCrypto.SigningBytes
