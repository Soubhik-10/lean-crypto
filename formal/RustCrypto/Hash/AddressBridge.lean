module
public import RustCrypto.Common.BigEndian
public import RustCrypto.Wots.Source
public import EthLib.Cryptography.Sphincs.TweakableHash
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.AddressBridge
open RustCrypto.WotsChain
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def native {n : Usize} (values : Aeneas.Std.Array U8 n) : Vector UInt8 n.val :=
  ⟨(values.val.map (fun b => UInt8.ofBitVec b.bv)).toArray, by simp⟩

@[simp] theorem native_list {n : Usize} (values : Aeneas.Std.Array U8 n) :
    (native values).toList = values.val.map (fun b => UInt8.ofBitVec b.bv) := by rfl

def headBytes (seed : Aeneas.Std.Array U8 16#usize) (layer : U32) (tree : U64)
    (tag pair word2 word3 : U32) : List U8 :=
  seed.val ++ (core.num.U32.to_be_bytes layer).val ++ List.replicate 4 0#u8 ++
    (core.num.U64.to_be_bytes tree).val ++ (core.num.U32.to_be_bytes tag).val ++
    (core.num.U32.to_be_bytes pair).val ++ (core.num.U32.to_be_bytes word2).val ++
    (core.num.U32.to_be_bytes word3).val

@[simp] theorem head_length (seed : Aeneas.Std.Array U8 16#usize) (layer : U32) (tree : U64)
    (tag pair word2 word3 : U32) : (headBytes seed layer tree tag pair word2 word3).length = 48 := by
  simp [headBytes]

theorem adrs_array (layer : UInt32) (tree : UInt64) (tag pair word2 word3 : UInt32) :
    (EthLib.Cryptography.Sphincs.encodeAdrs layer tree tag pair word2 word3).toArray =
      (EthLib.Cryptography.Sphincs.toByte 4 layer.toNat).toArray ++
      (EthLib.Cryptography.Sphincs.toByte 12 tree.toNat).toArray ++
      (EthLib.Cryptography.Sphincs.toByte 4 tag.toNat).toArray ++
      (EthLib.Cryptography.Sphincs.toByte 4 pair.toNat).toArray ++
      (EthLib.Cryptography.Sphincs.toByte 4 word2.toNat).toArray ++
      (EthLib.Cryptography.Sphincs.toByte 4 word3.toNat).toArray := by rfl

/-- The source 48-byte hash prefix is exactly PK.seed followed by EthLib's FIPS address. -/
theorem canonical_prefix (seed : Aeneas.Std.Array U8 16#usize) (layer : U32) (tree : U64)
    (tag pair word2 word3 : U32) :
    (headBytes seed layer tree tag pair word2 word3).map (fun b => UInt8.ofBitVec b.bv) =
      (native seed).toList ++ (EthLib.Cryptography.Sphincs.encodeAdrs
        (UInt32.ofBitVec layer.bv) (UInt64.ofBitVec tree.bv)
        (UInt32.ofBitVec tag.bv) (UInt32.ofBitVec pair.bv)
        (UInt32.ofBitVec word2.bv) (UInt32.ofBitVec word3.bv)).toList := by
  change _ = (native seed).toList ++
    (EthLib.Cryptography.Sphincs.encodeAdrs
      (UInt32.ofBitVec layer.bv) (UInt64.ofBitVec tree.bv)
      (UInt32.ofBitVec tag.bv) (UInt32.ofBitVec pair.bv)
      (UInt32.ofBitVec word2.bv) (UInt32.ofBitVec word3.bv)).toArray.toList
  rw [adrs_array]
  simp [headBytes, native_list, ByteBridge.encode32, ByteBridge.encode64,
    List.append_assoc]
  simpa only [Vector.toList, List.append_assoc, List.cons_append, List.nil_append] using
    congrArg (fun middle => (EthLib.Cryptography.Sphincs.toByte 4 layer.val).toList ++ middle ++
      (EthLib.Cryptography.Sphincs.toByte 4 tag.val).toList ++
      (EthLib.Cryptography.Sphincs.toByte 4 pair.val).toList ++
      (EthLib.Cryptography.Sphincs.toByte 4 word2.val).toList ++
      (EthLib.Cryptography.Sphincs.toByte 4 word3.val).toList) (ByteBridge.tree96 tree).symm

end RustCrypto.AddressBridge
