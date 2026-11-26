module
public import RustCrypto.CounterBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[irreducible] def searchChoice (source : Option (U32 × WotsSignSource.Digits))
    (reference : Option (UInt32 × EthLib.Cryptography.Sphincs.Codeword)) : Prop :=
  match source,reference with
  | none,none => True
  | some (counter,digits),some (refCounter,code) =>
      UInt32.ofBitVec counter.bv = refCounter ∧ digitsAgree digits code
  | _,_ => False

@[simp] theorem native_counter_word (n : Nat) :
    UInt32.ofBitVec (CounterSearch.counterWord n).bv = UInt32.ofNat n := by rfl

theorem ref_search_zero (seed : EthLib.Cryptography.Sphincs.PkSeed)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) (start : Nat) :
    EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
      seed key (nativeNode message) start 0 = none := by rfl

theorem find_first_succ {κ β : Type} (trial : Nat → κ) (test : κ → Id (Option β))
    (start fuel : Nat) :
    EthLib.Cryptography.Wots.findFirst trial test start (fuel+1) =
      match test (trial start) with
      | some digits => some (trial start,digits)
      | none => EthLib.Cryptography.Wots.findFirst trial test (start+1) fuel := by rfl

theorem ref_search_succ (seed : EthLib.Cryptography.Sphincs.PkSeed)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) (start fuel : Nat) :
    EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
      seed key (nativeNode message) start (fuel+1) =
      match EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId
        seed key (nativeNode message) (UInt32.ofNat start) with
      | some digits => some (UInt32.ofNat start,digits)
      | none => EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
          seed key (nativeNode message) (start+1) fuel := by
  unfold EthLib.Cryptography.Sphincs.Internal.findCounter
  generalize htest : EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId
    seed key (nativeNode message) = test
  have hg := find_first_succ UInt32.ofNat test start fuel
  cases hcase : test (UInt32.ofNat start) <;> simpa only [hcase] using hg

/-- The complete source counter search agrees with canonical EthLib, including wrap and exhaustion. -/
theorem search_ethlib (headBytes : List U8) (message : Node)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : headBytes.map (fun b => UInt8.ofBitVec b.bv) =
      seed.toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList)
    (fuel : Nat) : ∀ start,
    searchChoice (CounterSearch.search headBytes message start fuel)
      (EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
        seed key (nativeNode message) start fuel) := by
  induction fuel with
  | zero =>
    intro start
    rw [CounterSearch.search_zero,ref_search_zero]
    simp only [searchChoice]
  | succ fuel ih =>
    intro start
    rw [CounterSearch.search_succ,ref_search_succ]
    have ht := accept_ethlib headBytes message (CounterSearch.counterWord start) seed key hprefix
    rw [native_counter_word] at ht
    cases ha : CounterSearch.accept headBytes message (CounterSearch.counterWord start) <;>
      cases hr : EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId
        seed key (nativeNode message) (UInt32.ofNat start)
    all_goals simp only [ha,hr,digitChoice] at ht
    · exact ih (start+1)
    · simp only [searchChoice]
      exact ⟨native_counter_word start,ht⟩

@[step] theorem find_encoding_ethlib_spec (address : Address) (message : Node) (limit : U64)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      seed.toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList) :
    lean_sphincs.wots.find_encoding address message limit ⦃ out =>
      searchChoice out.1 (EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
        seed key (nativeNode message) 0 limit.val) ∧ out.2.val.take 48 = address.val.take 48 ⦄ := by
  apply WP.spec_mono (CounterSearch.find_encoding_spec address message limit)
  rintro ⟨result,next⟩ ⟨hresult,hnext⟩
  rw [hresult]
  exact ⟨search_ethlib (address.val.take 48) message seed key hprefix limit.val 0,hnext⟩

end RustCrypto.WotsEthlib
