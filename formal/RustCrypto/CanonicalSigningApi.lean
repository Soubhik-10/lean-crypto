module
public import RustCrypto.CanonicalSigningSuccess
public import RustCrypto.CanonicalPublicKey
public import RustCrypto.FullSign
public import RustCrypto.WholeVerifyDecoded
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.CanonicalCorrectness
open EthLib.Cryptography.Sphincs RustCrypto.WotsEthlib RustCrypto.TweakableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

/-- The bytes of any successful canonical signing result decode to a signature accepted by verification. -/
theorem successful_source_bytes_verify (secret message key : Aeneas.Std.Array U8 32#usize)
    (signed : Aeneas.Std.Array U8 7740#usize) (limit : Nat)
    (hkey : RustCrypto.bytes key.val = encodePublicKey (KeyGen.publicKey (nativeSeed secret)))
    (hsuccess : FullSign.Native.signWithLimit (nativeSeed secret) (nativeSeed message) limit =
      .ok (FullSign.nativeBytes signed.val)) :
    WholeVerifier.decodedVerify key message signed.val = true := by
  obtain ⟨sig,hencoded,hverifies⟩ := native_sign_success (nativeSeed secret) (nativeSeed message) limit _ hsuccess
  have hbytes : RustCrypto.bytes signed.val = encodeSignature sig := by
    apply ByteArray.ext
    apply _root_.Array.toList_inj.1
    rw [source_bytes_list]
    exact hencoded
  unfold WholeVerifier.decodedVerify
  rw [hkey,hbytes,public_key_decode_encode,signature_roundtrip]
  exact hverifies

/-- Run the actual public bounded signer and verifier, preserving an exhausted-counter error. -/
def signVerifyWithLimit (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64) :
    Result (core.result.Result Bool lean_sphincs.signing.SignError) := do
  let key ← lean_sphincs.signing.key_gen secret
  let result ← lean_sphincs.signing.sign_with_limit secret message limit
  match result with
  | .Err error => ok (.Err error)
  | .Ok signed =>
    let accepted ← lean_sphincs.verify key message signed.to_slice
    ok (.Ok accepted)

/-- A successful result from the actual bounded signer is accepted by the actual verifier. -/
@[step] theorem sign_with_limit_roundtrip_with_contract (recovery : WholeVerifier.RootContract)
    (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64) :
    signVerifyWithLimit secret message limit ⦃ out => match out with
      | .Err _ => True
      | .Ok accepted => accepted = true ⦄ := by
  unfold signVerifyWithLimit
  step with KeyGen.key_gen_ethlib_spec secret as ⟨key,hkey⟩
  step with FullSign.sign_with_limit_ethlib_spec secret message limit as ⟨result,hresult⟩
  cases result with
  | Err error => simp only [WP.spec_ok]
  | Ok signed =>
    have hsuccess : FullSign.Native.signWithLimit (nativeSeed secret) (nativeSeed message) limit.val =
        .ok (FullSign.nativeBytes signed.val) := hresult.symm
    have hv := successful_source_bytes_verify secret message key signed limit.val hkey hsuccess
    step with WholeVerifier.verify_decoded_with_recovery recovery key message signed.to_slice as ⟨accepted,haccepted⟩
    simp only [Aeneas.Std.Array.to_slice,Slice.from_val] at haccepted
    exact haccepted.trans hv

/-- Run the actual default signer and verifier, preserving an exhausted-counter error. -/
def signVerify (secret message : Aeneas.Std.Array U8 32#usize) :
    Result (core.result.Result Bool lean_sphincs.signing.SignError) := do
  let key ← lean_sphincs.signing.key_gen secret
  let result ← lean_sphincs.signing.sign secret message
  match result with
  | .Err error => ok (.Err error)
  | .Ok signed =>
    let accepted ← lean_sphincs.verify key message signed.to_slice
    ok (.Ok accepted)

/-- The actual default signer also produces only signatures accepted by the actual verifier. -/
@[step] theorem sign_roundtrip_with_contract (recovery : WholeVerifier.RootContract)
    (secret message : Aeneas.Std.Array U8 32#usize) :
    signVerify secret message ⦃ out => match out with
      | .Err _ => True
      | .Ok accepted => accepted = true ⦄ := by
  unfold signVerify
  step with KeyGen.key_gen_ethlib_spec secret as ⟨key,hkey⟩
  step with FullSign.sign_ethlib_spec secret message as ⟨result,hresult⟩
  cases result with
  | Err error => simp only [WP.spec_ok]
  | Ok signed =>
    have hsuccess : FullSign.Native.signWithLimit (nativeSeed secret) (nativeSeed message) 4294967296 =
        .ok (FullSign.nativeBytes signed.val) := hresult.symm
    have hv := successful_source_bytes_verify secret message key signed 4294967296 hkey hsuccess
    step with WholeVerifier.verify_decoded_with_recovery recovery key message signed.to_slice as ⟨accepted,haccepted⟩
    simp only [Aeneas.Std.Array.to_slice,Slice.from_val] at haccepted
    exact haccepted.trans hv

end RustCrypto.CanonicalCorrectness
