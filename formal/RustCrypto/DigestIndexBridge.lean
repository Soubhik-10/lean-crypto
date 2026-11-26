module
public import RustCrypto.MessageHashBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.MessageHashBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def rawTree (digest : Aeneas.Std.Array U8 34#usize) : Nat :=
  (65536*(digest.val[30]!).val+256*(digest.val[31]!).val+(digest.val[32]!).val)%262144

def rawLeaf (digest : Aeneas.Std.Array U8 34#usize) : Nat := (digest.val[33]!).val

theorem tail_four (digest : Aeneas.Std.Array U8 34#usize) : digest.val.drop 30 =
    [digest.val[30]!,digest.val[31]!,digest.val[32]!,digest.val[33]!] := by
  have hl : digest.val.length = 34 := digest.property
  apply List.ext_getElem
  · simp only [List.length_drop,hl]
    rfl
  · intro j hj hother
    have hj4 : j < 4 := by simpa only [List.length_drop,hl] using hj
    interval_cases j <;> simp (disch := omega) [getElem!_pos]

theorem digest_tree_native (digest : Aeneas.Std.Array U8 34#usize) :
    EthLib.Cryptography.Sphincs.digestTree (ForsDigest.nativeDigest digest) = rawTree digest := by
  unfold EthLib.Cryptography.Sphincs.digestTree
  rw [native_digest_list]
  change EthLib.Base.ByteOrder.ofBE (((digest.val.map (fun b => UInt8.ofBitVec b.bv)).drop 30).take 3)%262144 = _
  rw [←List.map_drop]
  rw [tail_four]
  simp only [List.map_cons,List.map_nil,List.take_succ_cons,List.take_zero]
  simp only [EthLib.Base.ByteOrder.ofBE,EthLib.Base.ByteOrder.ofBE.go,EthLib.Base.ByteOrder.ofBE.horner,
    List.foldl_cons,List.foldl_nil,UInt8.toNat_ofBitVec,Nat.shiftLeft_eq,Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
  unfold rawTree
  simp only [U8.bv_toNat]
  congr 1
  omega

theorem digest_leaf_native (digest : Aeneas.Std.Array U8 34#usize) :
    EthLib.Cryptography.Sphincs.digestLeaf (ForsDigest.nativeDigest digest) = rawLeaf digest := by
  unfold EthLib.Cryptography.Sphincs.digestLeaf
  rw [native_digest_list]
  have hd : digest.val.drop 33 = [digest.val[33]!] := by
    have ht := congrArg (List.drop 3) (tail_four digest)
    simpa [List.drop_drop] using ht
  change EthLib.Base.ByteOrder.ofBE (((digest.val.map (fun b => UInt8.ofBitVec b.bv)).drop 33).take 1)%256 = _
  rw [←List.map_drop]
  rw [hd]
  simp only [List.map_cons,List.map_nil,List.take_succ_cons,List.take_zero,
    EthLib.Base.ByteOrder.ofBE,EthLib.Base.ByteOrder.ofBE.go,EthLib.Base.ByteOrder.ofBE.horner,
    List.foldl_cons,List.foldl_nil,UInt8.toNat_ofBitVec,Nat.shiftLeft_eq,Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
  have hb : (digest.val[33]!).bv.toNat < 256 := by
    simpa only [UScalar.val] using (show (digest.val[33]!).val < 256 by scalar_tac)
  simpa only [rawLeaf,UScalar.val] using Nat.mod_eq_of_lt hb

theorem digest_index_native (digest : Aeneas.Std.Array U8 34#usize) :
    EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest) = rawTree digest*256+rawLeaf digest := by
  simp only [EthLib.Cryptography.Sphincs.digestIndex,digest_tree_native,digest_leaf_native,
    EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT]

end RustCrypto.MessageHashBridge
