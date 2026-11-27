module
public import RustCrypto.Common.ByteRelations
public import EthLib.Cryptography.Sphincs.Address
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ByteBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem encode32 (value : U32) :
    (core.num.U32.to_be_bytes value).val.map (fun b => UInt8.ofBitVec b.bv) =
      (EthLib.Cryptography.Sphincs.toByte 4 value.val).toList := by
  simp [core.num.U32.to_be_bytes, BitVec.toBEBytes, BitVec.toLEBytes,
    EthLib.Cryptography.Sphincs.toByte, EthLib.Base.ByteOrder.toBE,
    EthLib.Base.ByteOrder.toBE.go]
  repeat' constructor
  all_goals apply UInt8.toNat_inj.1
  all_goals simp only [UInt8.toNat_ofBitVec, UInt8.toNat_ofNat',
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals change _ = _ % 256
  all_goals norm_num1
  all_goals simp only [UScalar.val, U32.bv]
  all_goals omega

theorem encode64 (value : U64) :
    (core.num.U64.to_be_bytes value).val.map (fun b => UInt8.ofBitVec b.bv) =
      (EthLib.Cryptography.Sphincs.toByte 8 value.val).toList := by
  simp [core.num.U64.to_be_bytes, BitVec.toBEBytes, BitVec.toLEBytes,
    EthLib.Cryptography.Sphincs.toByte, EthLib.Base.ByteOrder.toBE,
    EthLib.Base.ByteOrder.toBE.go]
  repeat' constructor
  all_goals apply UInt8.toNat_inj.1
  all_goals simp only [UInt8.toNat_ofBitVec, UInt8.toNat_ofNat',
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  all_goals change _ = _ % 256
  all_goals norm_num1
  all_goals simp only [UScalar.val, U64.bv]
  all_goals omega

/-- The 96-bit address tree field has four leading zero bytes for every source u64. -/
theorem tree96 (value : U64) :
    (EthLib.Cryptography.Sphincs.toByte 12 value.val).toList =
      [0,0,0,0] ++ (EthLib.Cryptography.Sphincs.toByte 8 value.val).toList := by
  have hb : value.val < 18446744073709551616 := by scalar_tac
  have hz : value.val / 18446744073709551616 = 0 := Nat.div_eq_of_lt hb
  simp [EthLib.Cryptography.Sphincs.toByte, EthLib.Base.ByteOrder.toBE,
    EthLib.Base.ByteOrder.toBE.go, Nat.div_div_eq_div_mul, hz]

end RustCrypto.ByteBridge
