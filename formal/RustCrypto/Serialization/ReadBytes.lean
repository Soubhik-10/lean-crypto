module
public import RustCrypto.Common.ByteBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ByteBridge
set_option maxHeartbeats 2000000

@[simp] theorem bytes_size (values : List U8) : (RustCrypto.bytes values).size = values.length := by
  simp only [RustCrypto.bytes, ByteArray.size, List.size_toArray, List.length_map]

@[simp] theorem bytes_get (values : List U8) (i : Nat) (hi : i < values.length) :
    (RustCrypto.bytes values)[i]'(by simpa using hi) = UInt8.ofBitVec (values[i]'hi).bv := by
  change ((values.map (fun value => UInt8.ofNat value.val)).toArray)[i]'(by simpa using hi) = _
  simp only [List.getElem_toArray, List.getElem_map, byte_native_eq]

@[simp] theorem byteAt_bytes (values : List U8) (i : Nat) :
    EthLib.Base.byteAtOrZero (RustCrypto.bytes values) i =
      ((values[i]?).map (fun value => UInt8.ofBitVec value.bv)).getD 0 := by
  by_cases hi : i < values.length
  · have hbi : i < (RustCrypto.bytes values).size := by simpa only [bytes_size] using hi
    simp only [EthLib.Base.byteAtOrZero, dite_eq_left hbi,
      getElem?_pos values i hi, Option.map_some, Option.getD_some]
    exact bytes_get values i hi
  · have hbi : ¬ i < (RustCrypto.bytes values).size := by simpa only [bytes_size] using hi
    have hout : values[i]? = none := List.getElem?_eq_none (by omega)
    simp only [EthLib.Base.byteAtOrZero, dite_eq_right hbi, hout,
      Option.map_none, Option.getD_none]

theorem byteAt_slice (values : List U8) (offset count i : Nat) (hi : i < count)
    (hroom : offset + count ≤ values.length) :
    EthLib.Base.byteAtOrZero (RustCrypto.bytes ((values.drop offset).take count)) i =
      EthLib.Base.byteAtOrZero (RustCrypto.bytes values) (offset+i) := by
  have hs : i < ((values.drop offset).take count).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hv : offset+i < values.length := by omega
  simp only [byteAt_bytes, getElem?_pos ((values.drop offset).take count) i hs, getElem?_pos values (offset+i) hv,
    Option.map_some, Option.getD_some, List.getElem_take, List.getElem_drop]

theorem laneAt_slice (values : List U8) (offset : Nat) (hroom : offset+8 ≤ values.length) :
    EthLib.Cryptography.Hash.Keccak.Internal.laneAt
      (RustCrypto.bytes ((values.drop offset).take 8)) 0 =
      EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes values) offset := by
  have hb (i : Nat) (hi : i < 8) := byteAt_slice values offset 8 i hi hroom
  simp (disch := omega) only [EthLib.Cryptography.Hash.Keccak.Internal.laneAt,
    hb, Nat.zero_add, Nat.add_zero]

theorem laneAt_beyond (values : List U8) (offset : Nat) (hpast : values.length ≤ offset) :
    EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes values) offset = 0 := by
  have hb (i : Nat) : EthLib.Base.byteAtOrZero (RustCrypto.bytes values) (offset+i) = 0 := by
    have hp : ¬ offset+i < (RustCrypto.bytes values).size := by rw [bytes_size]; omega
    simp only [EthLib.Base.byteAtOrZero, dite_eq_right hp]
  have hzero : EthLib.Base.byteAtOrZero (RustCrypto.bytes values) offset = 0 := hb 0
  simp only [EthLib.Cryptography.Hash.Keccak.Internal.laneAt, hzero,
    hb 1, hb 2, hb 3, hb 4, hb 5, hb 6, hb 7]
  decide

end RustCrypto.ByteBridge
