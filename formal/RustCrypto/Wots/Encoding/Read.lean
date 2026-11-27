module
public import RustCrypto.Wots.Encoding.CounterBytes
public import RustCrypto.Wots.Encoding.EncodingBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def counterBytes (bytes : List U8) : Aeneas.Std.Array U8 4#usize :=
  Aeneas.Std.Array.from (List.ofFn (fun i : Fin 4 => bytes[i.val]!)) (by simp)

theorem counterBytes_val (bytes : List U8) (hroom : 4 ≤ bytes.length) : (counterBytes bytes).val = bytes.take 4 := by
  apply List.ext_getElem
  · simp only [counterBytes,Aeneas.Std.Array.from_val,List.length_ofFn,List.length_take]
    omega
  · intro i hi hother
    simp only [counterBytes,Aeneas.Std.Array.from_val,List.getElem_ofFn,List.getElem_take]
    rw [getElem!_pos bytes i (by simp only [List.length_take] at hother; omega)]

def nativeCounter (bytes : List U8) : UInt32 := UInt32.ofBitVec (core.num.U32.from_be_bytes (counterBytes bytes)).bv

def encoding (bytes : List U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) :
    Option EthLib.Cryptography.Sphincs.Codeword :=
  EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key (nativeNode message) (nativeCounter bytes)

def expectedLeaf (bytes : List U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) :
    Option EthLib.Cryptography.Sphincs.Digest :=
  if 1028 ≤ bytes.length then EthLib.Cryptography.Sphincs.otsLeaf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key
    (nativeNode message) (nativeCounter bytes) (nativeValues (bytes.drop 4)) else none

def consumed (unit : Nat) (bytes : List U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) : Nat :=
  if bytes.length < 4 then 0
  else if (encoding bytes seed key message).isNone then 4
  else if 1028 ≤ bytes.length then 1028 else 4+unit*((bytes.length-4)/unit)

theorem encoded_raw_native (address : Address) (counter : Aeneas.Std.Array U8 4#usize) (message seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList) :
    nativeNode (CounterSearch.encoded (address.val.take 48) message counter) =
      EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (EthLib.Cryptography.Sphincs.adrsEnc key)
        (EthLib.Base.packBytes (nativeNode message) ++ EthLib.Base.packBytes
          (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN
            (UInt32.ofBitVec (core.num.U32.from_be_bytes counter).bv).toNat)) := by
  have h := encoded_native (address.val.take 48) message (core.num.U32.from_be_bytes counter) (nativeNode seed) key hprefix
  simpa only [counter_bytes_roundtrip] using h

@[step] theorem encode_counter_spec (address : Address) (counter : Aeneas.Std.Array U8 4#usize) (message seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList) :
    lean_sphincs.hash.HashContext.encode address message counter ⦃ out =>
      EthLib.Cryptography.Sphincs.codeword? (nativeNode out.1) =
        EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key (nativeNode message)
          (UInt32.ofBitVec (core.num.U32.from_be_bytes counter).bv) ∧ out.2.val.take 48 = address.val.take 48 ⦄ := by
  apply WP.spec_mono (CounterSearch.encode_node_spec address message counter)
  rintro ⟨code,next⟩ ⟨hcode,hnext⟩
  constructor
  · rw [hcode,encoded_raw_native address counter message seed key hprefix]
    rfl
  · exact hnext

@[step] theorem codeword_native_spec (code : Node) : lean_sphincs.wots.codeword code ⦃ out =>
    out.map (fun digits => digits.val.map UScalar.val) =
      (EthLib.Cryptography.Sphincs.codeword? (nativeNode code)).map (fun word => word.toList.map Fin.val) ⦄ := by
  apply WP.spec_mono (RustCrypto.Codeword.codeword_ethlib_spec code)
  intro out hout
  simpa only [digest_adapter] using hout

end RustCrypto.WotsRecover
