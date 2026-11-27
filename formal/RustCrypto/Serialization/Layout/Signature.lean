module
public import RustCrypto.Serialization.Layout.Layer
public import RustCrypto.Serialization.Layout.Fors
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

/-- The structured public key represented by the source's fixed-size byte array. -/
def publicKey (bytes : Aeneas.Std.Array U8 32#usize) : EthLib.Cryptography.Sphincs.PublicKey :=
  ⟨nativeNode (MessageHashBridge.keySeed bytes),nativeNode (MessageHashBridge.keyRoot bytes)⟩

/-- The reference decoder reads exactly the source seed and root. -/
theorem public_key_decode (bytes : Aeneas.Std.Array U8 32#usize) :
    EthLib.Cryptography.Sphincs.decodePublicKey (RustCrypto.bytes bytes.val) = .ok (publicKey bytes) := by
  have hl : bytes.val.length = 32 := bytes.property
  have hs : (RustCrypto.bytes bytes.val).size = EthLib.Cryptography.Sphincs.Constants.PUB_KEY_SIZE := by
    rw [ByteBridge.bytes_size,hl]
    rfl
  unfold EthLib.Cryptography.Sphincs.decodePublicKey
  rw [dite_eq_left hs]
  have hseed := node_read bytes.val 0 (by omega)
  have hroot := node_read bytes.val 16 (by omega)
  unfold publicKey MessageHashBridge.keySeed MessageHashBridge.keyRoot
  rw [hseed,hroot]
  rfl

/-- Every source signature field at its production byte offset. -/
def signature (bytes : List U8) : EthLib.Cryptography.Sphincs.Signature :=
  ⟨nativeNode (ForsRead.nodeAt bytes 0),ForsRead.decodedOpenings (bytes.drop 16),
   LayerInput.signature (bytes.drop 4240) .bottom,
   LayerInput.signature (bytes.drop 5396) .middle,
   LayerInput.signature (bytes.drop 6552) .top⟩

/-- Every 7740-byte source string decodes to the same counter, chain, path and FORS fields. -/
theorem signature_decode (bytes : List U8) (hl : bytes.length = 7740) :
    EthLib.Cryptography.Sphincs.decodeSignature (RustCrypto.bytes bytes) = .ok (signature bytes) := by
  have hs : (RustCrypto.bytes bytes).size = EthLib.Cryptography.Sphincs.Constants.SIG_SIZE := by
    rw [ByteBridge.bytes_size,hl]
    rfl
  unfold EthLib.Cryptography.Sphincs.decodeSignature
  rw [dite_eq_left hs]
  have hr := node_read bytes 0 (by omega)
  have hf := fors_decode bytes 16 (by omega)
  have hb := layer_signature_decode bytes 4240 .bottom (by rw [hl]; decide)
  have hm := layer_signature_decode bytes 5396 .middle (by rw [hl]; decide)
  have ht := layer_signature_decode bytes 6552 .top (by rw [hl]; decide)
  unfold signature
  rw [hr,←hf,hb,hm,ht]
  rfl

/-- The reference decoder's complete length behavior, including malformed lengths. -/
theorem signature_decode_total (bytes : List U8) :
    EthLib.Cryptography.Sphincs.decodeSignature (RustCrypto.bytes bytes) =
      if bytes.length = 7740 then .ok (signature bytes)
      else .error (.badSignatureSize bytes.length) := by
  by_cases hl : bytes.length = 7740
  · rw [ite_eq_left hl,signature_decode bytes hl]
  · unfold EthLib.Cryptography.Sphincs.decodeSignature
    have hs : (RustCrypto.bytes bytes).size ≠ EthLib.Cryptography.Sphincs.Constants.SIG_SIZE := by
      rw [ByteBridge.bytes_size]
      exact hl
    rw [dite_eq_right hs,ite_eq_right hl,ByteBridge.bytes_size]

end RustCrypto.Layout
