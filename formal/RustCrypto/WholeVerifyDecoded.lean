module
public import RustCrypto.WholeVerifyApi
public import RustCrypto.LayoutSignature
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 100000
set_option maxRecDepth 8192

/-- Reference byte-facing verification, including both decoder error branches. -/
def decodedVerify (key message : Aeneas.Std.Array U8 32#usize) (bytes : List U8) : Bool :=
  match EthLib.Cryptography.Sphincs.decodePublicKey (RustCrypto.bytes key.val),
    EthLib.Cryptography.Sphincs.decodeSignature (RustCrypto.bytes bytes) with
  | .ok pk, .ok sig => EthLib.Cryptography.Sphincs.verifyWith EthLib.Cryptography.Sphincs.hashId pk (nativeSeed message) sig
  | _, _ => false

/-- The complete decoder-facing specification equals the native whole-verifier model. -/
theorem expected_verify_decoded (key message : Aeneas.Std.Array U8 32#usize) (bytes : List U8) :
    expectedVerify key message bytes = decodedVerify key message bytes := by
  unfold decodedVerify
  rw [Layout.public_key_decode,Layout.signature_decode_total]
  unfold expectedVerify
  by_cases h : bytes.length = 7740
  · simp only [ite_eq_left h]
    rfl
  · simp only [ite_eq_right h]

/-- Every signature length, using the actual reference public-key and signature decoders. -/
@[step] theorem verify_decoded_with_recovery (recovery : RootContract)
    (key message : Aeneas.Std.Array U8 32#usize) (bytes : Slice U8) :
    lean_sphincs.verify key message bytes ⦃ out => out = decodedVerify key message bytes.val ⦄ := by
  apply WP.spec_mono (verify_with_recovery recovery key message bytes)
  intro out hout
  exact hout.trans (expected_verify_decoded key message bytes.val)

end RustCrypto.WholeVerifier
