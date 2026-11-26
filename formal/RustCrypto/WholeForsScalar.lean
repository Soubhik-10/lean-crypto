module
public import RustCrypto.WholeVerifyModel
public import RustCrypto.ForsScalarTotal
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem fors_scalar_contract : ForsContract := by
  intro address reader digest seed index hframe
  apply WP.spec_mono (ForsScalar.recover_fors_total_spec address reader digest seed index hframe)
  rintro out ⟨hresult,hnextFrame,hreader⟩
  refine ⟨?_,hnextFrame,?_⟩
  · simpa only [ForsScalar.canonicalRecover] using hresult
  · intro hsome
    have hroom : 4224 ≤ reader.val.length := by
      by_contra h
      cases he : out.1 with
      | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hsome
      | some node => simp only [he,Option.map_some,ite_eq_right h] at hresult; contradiction
    simpa only [ite_eq_left hroom] using hreader

end RustCrypto.WholeVerifier
