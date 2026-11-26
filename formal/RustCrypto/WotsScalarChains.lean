module
public import RustCrypto.WotsScalarShort
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem scalar_chains_success_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hreader : 1024 ≤ reader.val.length) (hdigits : digitRelation digits word) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains address reader digits ends ⦃ out =>
      out.1 = some () ∧ keyFrame out.2.1 seed key .wotsHash ∧ out.2.2.1.val = reader.val.drop 1024 ∧
      nativeBytes out.2.2.2 = nativeBytes ends ++ endsBefore reader.val word seed key 64 ⦄ := by
  unfold lean_sphincs.wots.recover_chains
  step with scalar_loop_spec address reader ends digits word seed key hreader hdigits hframe
    as ⟨status,nextAddress,remaining,nextEnds,hstatus,hnextFrame,hremaining,hends⟩
  exact ⟨hstatus,hnextFrame,hremaining,hends⟩

@[step] theorem scalar_chains_short_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hreader : reader.val.length < 1024) (hdigits : digitRelation digits word) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains address reader digits ends ⦃ out =>
      out.1 = none ∧ keyFrame out.2.1 seed key .wotsHash ∧ out.2.2.1.val = reader.val.drop (16*(reader.val.length/16)) ⦄ := by
  unfold lean_sphincs.wots.recover_chains
  step with scalar_short_loop_spec address reader ends digits word seed key hreader hdigits hframe
    as ⟨status,nextAddress,remaining,nextEnds,hstatus,hnextFrame,hremaining⟩
  exact ⟨hstatus,hnextFrame,hremaining⟩

/-- Complete non-AVX2 source WOTS chain recovery, including every reader length. -/
@[step] theorem scalar_chains_total_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hdigits : digitRelation digits word) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains address reader digits ends ⦃ out =>
      out.1 = (if 1024 ≤ reader.val.length then some () else none) ∧ keyFrame out.2.1 seed key .wotsHash ∧
      out.2.2.1.val = reader.val.drop (if 1024 ≤ reader.val.length then 1024 else 16*(reader.val.length/16)) ∧
      (1024 ≤ reader.val.length → nativeBytes out.2.2.2 = nativeBytes ends ++ endsBefore reader.val word seed key 64) ⦄ := by
  by_cases hroom : 1024 ≤ reader.val.length
  · apply WP.spec_mono (scalar_chains_success_spec address reader ends digits word seed key hroom hdigits hframe)
    rintro out ⟨hstatus,hnextFrame,hremaining,hends⟩
    refine ⟨?_,hnextFrame,?_,?_⟩
    · simpa only [ite_eq_left hroom] using hstatus
    · simpa only [ite_eq_left hroom] using hremaining
    · exact fun _ => hends
  · apply WP.spec_mono (scalar_chains_short_spec address reader ends digits word seed key (by omega) hdigits hframe)
    rintro out ⟨hstatus,hnextFrame,hremaining⟩
    refine ⟨?_,hnextFrame,?_,?_⟩
    · simpa only [ite_eq_right hroom] using hstatus
    · simpa only [ite_eq_right hroom] using hremaining
    · exact fun h => False.elim (hroom h)

end RustCrypto.WotsRecover
