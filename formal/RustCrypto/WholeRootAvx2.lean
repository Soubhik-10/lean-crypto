module
public import RustCrypto.WholeRoot
public import RustCrypto.WholeVerifyDecoded
public import RustCrypto.WholeForsSimd
public import RustCrypto.WotsAvx2Entry
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier

theorem recover_root_avx2_contract : RootContract :=
  recover_root_with_backends 256 WotsRecover.avx2_backend_contract fors_simd_contract

/-- Complete actual verifier equivalence for every signature byte string. -/
@[step] theorem verify_avx2_ethlib_spec (key message : Aeneas.Std.Array U8 32#usize) (bytes : Slice U8) :
    lean_sphincs.verify key message bytes ⦃ out => out =
      match EthLib.Cryptography.Sphincs.decodePublicKey (RustCrypto.bytes key.val),
        EthLib.Cryptography.Sphincs.decodeSignature (RustCrypto.bytes bytes.val) with
      | .ok pk, .ok sig => EthLib.Cryptography.Sphincs.verifyWith EthLib.Cryptography.Sphincs.hashId pk
          (RustCrypto.WotsEthlib.nativeSeed message) sig
      | _, _ => false ⦄ :=
  verify_decoded_with_recovery recover_root_avx2_contract key message bytes

end RustCrypto.WholeVerifier
