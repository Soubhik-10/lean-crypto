module
public import RustCrypto.WotsSignBridge
public import RustCrypto.CodewordBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem digest_adapter (code : Node) : Codeword.asDigest code = nativeNode code := by
  apply Vector.ext
  intro i hi
  simp [Codeword.asDigest,nativeNode,ByteBridge.byte_native_eq]

theorem enc_head_native (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) :
    (typedKeyHead seed key 7#u32 0 0).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList := by
  have h := canonical_prefix seed (stepWord key.layer.toNat) (treeWord key.tree) 7#u32
    (stepWord key.leaf) (stepWord 0) (stepWord 0)
  have hseven : UInt32.ofBitVec (7#u32).bv = 7 := by rfl
  simpa only [typedKeyHead, native_list, native_node_list, native_step_word, native_tree_word, hseven,
    EthLib.Cryptography.Sphincs.adrsEnc, EthLib.Cryptography.Sphincs.keyAdrs,
    EthLib.Cryptography.Sphincs.adrs, EthLib.Cryptography.Sphincs.AdrsType.code] using h

theorem counter_bytes_native (counter : U32) :
    (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN
      (UInt32.ofBitVec counter.bv).toNat).toArray.toList =
        (core.num.U32.to_be_bytes counter).val.map (fun b => UInt8.ofBitVec b.bv) := by
  rw [show EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN = 4 by rfl]
  exact (ByteBridge.encode32 counter).symm

theorem encoding_preimage (headBytes : List U8) (message : Node) (counter : U32)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : headBytes.map (fun b => UInt8.ofBitVec b.bv) =
      seed.toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList) :
    RustCrypto.bytes (headBytes ++ message.val ++ (core.num.U32.to_be_bytes counter).val) =
      EthLib.Cryptography.Sphincs.thInput seed (EthLib.Cryptography.Sphincs.adrsEnc key)
        (EthLib.Base.packBytes (nativeNode message) ++ EthLib.Base.packBytes
          (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN
            (UInt32.ofBitVec counter.bv).toNat)) := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  simp_all [EthLib.Cryptography.Sphincs.thInput, EthLib.Base.packBytes,
    source_bytes_list, nativeNode, Vector.toList, List.map_append, List.append_assoc]
  exact (counter_bytes_native counter).symm

theorem encoded_native (headBytes : List U8) (message : Node) (counter : U32)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : headBytes.map (fun b => UInt8.ofBitVec b.bv) =
      seed.toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList) :
    nativeNode (CounterSearch.encoded headBytes message (core.num.U32.to_be_bytes counter)) =
      EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId seed
        (EthLib.Cryptography.Sphincs.adrsEnc key)
        (EthLib.Base.packBytes (nativeNode message) ++ EthLib.Base.packBytes
          (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN
            (UInt32.ofBitVec counter.bv).toNat)) := by
  apply Vector.toList_inj.1
  rw [native_node_list]
  simp only [CounterSearch.encoded,Aeneas.Std.Array.from_val]
  rw [List.map_take,ByteBridge.digest_native,th_pure_list,
    encoding_preimage headBytes message counter seed key hprefix]

end RustCrypto.WotsEthlib
