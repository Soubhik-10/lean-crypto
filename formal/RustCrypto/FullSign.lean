module
public import RustCrypto.FullSignPublic
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem public_refinement_native (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64)
    (out : core.result.Result (Aeneas.Std.Array U8 7740#usize) lean_sphincs.signing.SignError)
    (h : publicRefinement secret message limit out) :
    nativeResult out = Native.signWithLimit (nativeSeed secret) (nativeSeed message) limit.val := by
  unfold publicRefinement at h
  obtain ⟨seed,rho,digest,hseed,hrho,hdigest,hresult⟩ := h
  rw [hresult]
  unfold signFromDigest initialBytes ForsSigning.canonicalSign Native.signWithLimit
  rw [stages_native]
  unfold KeyGen.publicKey at hdigest
  simp only [hdigest,hseed,hrho]
  congr 5

/-- The actual public bounded signer is total and returns exactly the canonical native signature bytes,
    or the first layer whose bounded counter search is exhausted. -/
@[step] theorem sign_with_limit_ethlib_spec (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64) :
    lean_sphincs.signing.sign_with_limit secret message limit ⦃ out =>
      nativeResult out = Native.signWithLimit (nativeSeed secret) (nativeSeed message) limit.val ⦄ := by
  apply WP.spec_mono (sign_with_limit_refinement secret message limit)
  intro out hout
  exact public_refinement_native secret message limit out hout

/-- Public signing uses the exact full 32-bit counter range, including every exhaustion path. -/
@[step] theorem sign_ethlib_spec (secret message : Aeneas.Std.Array U8 32#usize) :
    lean_sphincs.signing.sign secret message ⦃ out =>
      nativeResult out = Native.signWithLimit (nativeSeed secret) (nativeSeed message) 4294967296 ⦄ := by
  unfold lean_sphincs.signing.sign
  step with counter_limit_spec as ⟨limit,hlimit⟩
  step with sign_with_limit_ethlib_spec secret message limit as ⟨out,hout⟩
  simpa only [hlimit] using hout

end RustCrypto.FullSign
