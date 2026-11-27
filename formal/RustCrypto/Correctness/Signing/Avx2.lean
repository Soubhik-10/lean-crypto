module
public import RustCrypto.Correctness.Signing.Api
public import RustCrypto.Verification.Root.Avx2
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.CanonicalCorrectness

/-- Actual key generation, bounded signing, and verification roundtrip on the avx2 source path. -/
@[step] theorem sign_with_limit_roundtrip_avx2 (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64) :
    signVerifyWithLimit secret message limit ⦃ out => match out with
      | .Err _ => True
      | .Ok accepted => accepted = true ⦄ :=
  sign_with_limit_roundtrip_with_contract WholeVerifier.recover_root_avx2_contract secret message limit

/-- Actual default signing and verification roundtrip on the avx2 source path. -/
@[step] theorem sign_roundtrip_avx2 (secret message : Aeneas.Std.Array U8 32#usize) :
    signVerify secret message ⦃ out => match out with
      | .Err _ => True
      | .Ok accepted => accepted = true ⦄ :=
  sign_roundtrip_with_contract WholeVerifier.recover_root_avx2_contract secret message

end RustCrypto.CanonicalCorrectness
