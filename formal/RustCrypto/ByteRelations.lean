module
public import RustCrypto.ReadBytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ByteBridge

def fromNative (value : UInt8) : U8 := ⟨value.toBitVec⟩

@[simp] theorem from_native_roundtrip (value : U8) :
    fromNative (UInt8.ofBitVec value.bv) = value := by
  cases value
  rfl

/-- Native byte embedding retains all source bytes, so equality is reflected. -/
theorem native_list_injective (left right : List U8)
    (h : left.map (fun value => UInt8.ofBitVec value.bv) =
      right.map (fun value => UInt8.ofBitVec value.bv)) : left = right := by
  have hinv := congrArg (List.map fromNative) h
  simpa only [List.map_map, Function.comp_def, from_native_roundtrip,
    List.map_id'] using hinv

@[simp] theorem native_digest_byte (value : UInt8) :
    UInt8.ofBitVec (⟨value.toNat, by have := value.toNat_lt; scalar_tac⟩ : U8).bv = value := by
  apply UInt8.toNat_inj.1
  rfl

/-- The concrete Alloy boundary uses exactly EthLib's digest bytes. -/
theorem digest_native (values : List U8) :
    (RustCrypto.digest values).val.map (fun value => UInt8.ofBitVec value.bv) =
      (EthLib.Cryptography.Hash.Keccak.keccak256 (RustCrypto.bytes values)).toList := by
  simp only [RustCrypto.digest, Aeneas.Std.Array.from_val, List.map_map,
    Function.comp_def, native_digest_byte, List.map_id']

end RustCrypto.ByteBridge
