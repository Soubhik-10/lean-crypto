module
public import RustCrypto.WholeVerifyModel
public import RustCrypto.WholeVerifyCompare
public import RustCrypto.Verifier
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

/-- Complete public Boolean verification once actual root recovery is established. -/
@[step] theorem verify_with_recovery (recovery : RootContract) (key message : Aeneas.Std.Array U8 32#usize) (bytes : Slice U8) :
    lean_sphincs.verify key message bytes ⦃ out => out = expectedVerify key message bytes.val ⦄ := by
  by_cases hsize : bytes.val.length = 7740
  · have hsourceSize : Slice.len bytes = lean_sphincs.SIGNATURE_BYTES := by
      apply UScalar.eq_of_val_eq
      simpa [lean_sphincs.SIGNATURE_BYTES] using hsize
    unfold lean_sphincs.verify
    simp only [ite_eq_left hsourceSize]
    step with recovery key message bytes hsize as ⟨root,hroot⟩
    step with option_compare_spec key root as ⟨result,hresult⟩
    have hexpected : root.map nativeNode = expectedRoot key message bytes.val := by
      simpa only [expectedRoot,ite_eq_left hsize] using hroot
    rw [hresult,hexpected]
    have hp : (fun value : EthLib.Cryptography.Sphincs.Digest =>
        decide (value = nativeNode (MessageHashBridge.keyRoot key))) =
        (fun value : EthLib.Cryptography.Sphincs.Digest => decide (value = (publicKey key).root)) := by
      funext value
      apply Bool.eq_iff_iff.mpr
      simp only [publicKey,decide_eq_true_eq]
      exact Iff.of_eq (decide_eq_true_eq (p := value = nativeNode (MessageHashBridge.keyRoot key))).symm
    rw [hp]
    exact (expected_verify_root key message bytes.val).symm
  · rw [Verifier.wrong_length_rejected key message bytes hsize,WP.spec_ok]
    simp only [expectedVerify,ite_eq_right hsize]

end RustCrypto.WholeVerifier
