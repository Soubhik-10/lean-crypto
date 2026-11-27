module
public import RustCrypto.Verification.Model
public import RustCrypto.Serialization.Layout.ForsSimd
public import RustCrypto.Fors.Forest.Total
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem fors_simd_contract : ForsContract := by
  intro address reader digest seed index hframe
  apply WP.spec_mono (ForsForest.recover_fors_total_spec address reader digest seed index hframe)
  rintro out ⟨hresult,hnextFrame,hreader⟩
  refine ⟨?_,hnextFrame,?_⟩
  · simpa only [Layout.simd_canonical_recover_scalar] using hresult
  · intro hsome
    have hroom : 4224 ≤ reader.val.length := by
      by_contra h
      cases he : out.1 with
      | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hsome
      | some node => simp only [he,Option.map_some,ite_eq_right h] at hresult; contradiction
    simpa only [ite_eq_left hroom] using hreader

end RustCrypto.WholeVerifier
