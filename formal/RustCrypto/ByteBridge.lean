module
public import LeanSphincs.Funs
public import Mathlib.Tactic.IntervalCases
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ByteBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def byte (value : U8) : UInt8 := UInt8.ofNat value.val

def word (value : U64) : UInt64 := UInt64.ofBitVec value.bv

@[simp] theorem byte_eq (value : U8) : byte value = UInt8.ofBitVec value.bv := by
  apply UInt8.toBitVec_inj.1
  change BitVec.ofNat 8 value.bv.toNat = value.bv
  simpa only [BitVec.setWidth_eq] using BitVec.ofNat_toNat 8 value.bv

@[simp] theorem byte_native_eq (value : U8) :
    UInt8.ofNat value.val = UInt8.ofBitVec value.bv := byte_eq value

theorem array_eight (input : Aeneas.Std.Array U8 8#usize) : input.val =
    [input.val[0]!, input.val[1]!, input.val[2]!, input.val[3]!,
     input.val[4]!, input.val[5]!, input.val[6]!, input.val[7]!] := by
  have hlen : input.val.length = 8 := input.property
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hother
    have hi8 : i < 8 := by omega
    interval_cases i <;> simp (disch := omega) [getElem!_pos]


theorem decode_values (b0 b1 b2 b3 b4 b5 b6 b7 : U8) :
    UInt64.ofBitVec (BitVec.fromLEBytes [b0.bv,b1.bv,b2.bv,b3.bv,b4.bv,b5.bv,b6.bv,b7.bv]) =
      EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes [b0,b1,b2,b3,b4,b5,b6,b7]) 0 := by
  change UInt64.ofBitVec (BitVec.fromLEBytes [b0.bv,b1.bv,b2.bv,b3.bv,b4.bv,b5.bv,b6.bv,b7.bv]) =
    (UInt8.ofNat b0.val).toUInt64 |||
    (UInt8.ofNat b1.val).toUInt64 <<< 8 |||
    (UInt8.ofNat b2.val).toUInt64 <<< 16 |||
    (UInt8.ofNat b3.val).toUInt64 <<< 24 |||
    (UInt8.ofNat b4.val).toUInt64 <<< 32 |||
    (UInt8.ofNat b5.val).toUInt64 <<< 40 |||
    (UInt8.ofNat b6.val).toUInt64 <<< 48 |||
    (UInt8.ofNat b7.val).toUInt64 <<< 56
  simp only [byte_native_eq]
  apply UInt64.toBitVec_inj.1
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt64, BitVec.fromLEBytes,
    List.length_cons, List.length_nil]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

/-- The source little-endian decoder and EthLib's lane reader agree on every eight bytes. -/
theorem decode_eight (input : Aeneas.Std.Array U8 8#usize) :
    word (core.num.U64.from_le_bytes input) =
      EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes input.val) 0 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hlist⟩ :
      ∃ b0 b1 b2 b3 b4 b5 b6 b7 : U8, input.val = [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨input.val[0]!, input.val[1]!, input.val[2]!, input.val[3]!,
     input.val[4]!, input.val[5]!, input.val[6]!, input.val[7]!, array_eight input⟩
  have hbits : (core.num.U64.from_le_bytes input).bv =
      BitVec.fromLEBytes [b0.bv,b1.bv,b2.bv,b3.bv,b4.bv,b5.bv,b6.bv,b7.bv] := by
    apply BitVec.eq_of_toNat_eq
    simp only [U64.bv, core.num.U64.from_le_bytes, BitVec.toNat_cast]
    rw [hlist]
    rfl
  unfold word
  rw [hbits, hlist]
  exact decode_values b0 b1 b2 b3 b4 b5 b6 b7

end RustCrypto.ByteBridge
