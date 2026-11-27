module
public import RustCrypto.Verification.Root.Model
public import RustCrypto.Verification.Fors.Simd
public import RustCrypto.Verification.Decoded
public import RustCrypto.Wots.Scalar.Entry
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier

theorem recover_root_sse2_contract : RootContract :=
  recover_root_with_backends 16 WotsRecover.scalar_backend_contract fors_simd_contract

/-- Complete actual SSE2 verifier equivalence, with every signature length and reference decoding. -/
@[step] theorem verify_sse2_decoded (key message : Aeneas.Std.Array U8 32#usize) (bytes : Slice U8) :
    lean_sphincs.verify key message bytes ⦃ out => out = decodedVerify key message bytes.val ⦄ :=
  verify_decoded_with_recovery recover_root_sse2_contract key message bytes

/-- Complete actual SSE2 verifier equivalence, stated directly against both reference decoders. -/
@[step] theorem verify_sse2_ethlib_spec (key message : Aeneas.Std.Array U8 32#usize) (bytes : Slice U8) :
    lean_sphincs.verify key message bytes ⦃ out => out =
      match EthLib.Cryptography.Sphincs.decodePublicKey (RustCrypto.bytes key.val),
        EthLib.Cryptography.Sphincs.decodeSignature (RustCrypto.bytes bytes.val) with
      | .ok pk, .ok sig => EthLib.Cryptography.Sphincs.verifyWith EthLib.Cryptography.Sphincs.hashId pk
          (RustCrypto.WotsEthlib.nativeSeed message) sig
      | _, _ => false ⦄ :=
  verify_decoded_with_recovery recover_root_sse2_contract key message bytes

end RustCrypto.WholeVerifier
