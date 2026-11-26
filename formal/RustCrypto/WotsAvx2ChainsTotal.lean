module
public import RustCrypto.WotsAvx2ChainsShort
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem chains_loop_total_spec (address : Address) (reader : Slice U8) (ends : List U8)
    (addresses : Aeneas.Std.Array Address 4#usize) (digits : WotsRecover.Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hdigits : WotsRecover.digitRelation digits word) (hframe : keyFrame address seed key .wotsHash)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop address reader digits ends addresses 0#usize ⦃ out =>
      out.1 = (if 1024 ≤ reader.val.length then some () else none) ∧ keyFrame out.2.1 seed key .wotsHash ∧
      out.2.2.1.val = reader.val.drop (if 1024 ≤ reader.val.length then 1024 else 256*(reader.val.length/256)) ∧
      (1024 ≤ reader.val.length → nativeBytes out.2.2.2 = nativeBytes ends ++ WotsRecover.endsBefore reader.val word seed key 64) ⦄ := by
  by_cases hroom : 1024 ≤ reader.val.length
  · apply WP.spec_mono (chains_loop_spec address reader ends addresses digits word seed key hroom hdigits hframe hframes)
    rintro out ⟨hstatus,hnextFrame,hremaining,hends⟩
    refine ⟨?_,hnextFrame,?_,?_⟩
    · simpa only [ite_eq_left hroom] using hstatus
    · simpa only [ite_eq_left hroom] using hremaining
    · exact fun _ => hends
  · apply WP.spec_mono (chains_short_loop_spec address reader ends addresses digits word seed key (by omega) hdigits hframe hframes)
    rintro out ⟨hstatus,hnextFrame,hremaining⟩
    refine ⟨?_,hnextFrame,?_,?_⟩
    · simpa only [ite_eq_right hroom] using hstatus
    · simpa only [ite_eq_right hroom] using hremaining
    · exact fun h => False.elim (hroom h)

/-- Full actual AVX2 recovery of all 64 chains, including every input length and the exact reader suffix. -/
@[step] theorem avx2_chains_total_spec (address : Address) (reader : Slice U8) (ends : List U8)
    (digits : WotsRecover.Digits) (word : EthLib.Cryptography.Sphincs.Codeword)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hdigits : WotsRecover.digitRelation digits word) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains address reader digits ends ⦃ out =>
      out.1 = (if 1024 ≤ reader.val.length then some () else none) ∧ keyFrame out.2.1 seed key .wotsHash ∧
      out.2.2.1.val = reader.val.drop (if 1024 ≤ reader.val.length then 1024 else 256*(reader.val.length/256)) ∧
      (1024 ≤ reader.val.length → nativeBytes out.2.2.2 = nativeBytes ends ++ WotsRecover.endsBefore reader.val word seed key 64) ⦄ := by
  unfold lean_sphincs.wots.recover_chains
  step with clone_array_spec address as ⟨addresses,haddresses⟩
  have hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash := by
    intro j hj
    rw [haddresses j hj]
    exact hframe
  step with chains_loop_total_spec address reader ends addresses digits word seed key hdigits hframe hframes
    as ⟨status,nextAddress,remaining,nextEnds,hstatus,hnextFrame,hremaining,hends⟩
  exact ⟨hstatus,hnextFrame,hremaining,hends⟩

end RustCrypto.WotsAvx2
