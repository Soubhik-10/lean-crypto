module
public import RustCrypto.Common.OrderedVector
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem chain_start_model (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) (oldTag : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = typedKeyHead seed key oldTag old2 old3) :
    nativeNode (WotsSource.chainStart address secret (stepWord key.leaf) (stepWord chain.val)).1 =
      EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (nativeSeed secret) (EthLib.Cryptography.Sphincs.adrsPrf key chain) ∧
    (WotsSource.chainStart address secret (stepWord key.leaf) (stepWord chain.val)).2.val.take 48 =
      keyHead seed key 0 0 := by
  obtain ⟨out,hmodel,hcanonical⟩ := WP.spec_exists (WP.spec_and
    (WotsSource.chain_start_spec address secret (stepWord key.leaf) (stepWord chain.val))
    (chain_start_ethlib_spec address seed secret key chain oldTag old2 old3 hhead))
  simpa only [hmodel] using hcanonical

@[irreducible] def publicEnd (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) :
    EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key chain 0 3
    (by simp [EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH])
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
      (nativeNode seed) (nativeSeed secret) (EthLib.Cryptography.Sphincs.adrsPrf key chain))

/-- Each source public-key iteration computes exactly one canonical chain endpoint. -/
theorem public_step_ethlib (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) (oldTag : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = typedKeyHead seed key oldTag old2 old3) :
    nativeNode (WotsSource.publicStep address secret (stepWord key.leaf) chain.val).1 =
      publicEnd seed secret key chain ∧
    ∃ word2 word3, (WotsSource.publicStep address secret (stepWord key.leaf) chain.val).2.val.take 48 =
      keyHead seed key word2 word3 := by
  have hs := chain_start_model address seed secret key chain oldTag old2 old3 hhead
  have hw := walk_ethlib seed key chain 3 0 0 0
    (WotsSource.chainStart address secret (stepWord key.leaf) (stepWord chain.val)).2
    (WotsSource.chainStart address secret (stepWord key.leaf) (stepWord chain.val)).1 hs.2
    (by simp [EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH])
  constructor
  · simpa only [WotsSource.publicStep, publicEnd, hs.1] using hw.1
  · exact hw.2

@[irreducible] def endBytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (start fuel : Nat) : List UInt8 :=
  (((List.ofFn (publicEnd seed secret key)).drop start).take fuel).flatMap Vector.toList

theorem end_bytes_zero (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (start : Nat) :
    endBytes seed secret key start 0 = [] := by simp [endBytes]

theorem end_bytes_succ (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (start fuel : Nat)
    (hstart : start < EthLib.Cryptography.Sphincs.Constants.V) :
    endBytes seed secret key start (fuel+1) =
      (publicEnd seed secret key ⟨start,hstart⟩).toList ++
        endBytes seed secret key (start+1) fuel := by
  unfold endBytes
  rw [List.drop_eq_getElem_cons (by simpa using hstart)]
  simp only [List.take_succ_cons, List.flatMap_cons, List.getElem_ofFn]

theorem collect_ethlib (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (fuel : Nat) :
    ∀ (start : Nat) (address : Address) (ends : List U8) (oldTag : U32) (old2 old3 : Nat),
      address.val.take 48 = typedKeyHead seed key oldTag old2 old3 →
      start+fuel ≤ EthLib.Cryptography.Sphincs.Constants.V →
    (WotsSource.publicCollect secret (stepWord key.leaf) fuel start address ends).2.map
        (fun b => UInt8.ofBitVec b.bv) = ends.map (fun b => UInt8.ofBitVec b.bv) ++
          endBytes seed secret key start fuel ∧
    ∃ tag word2 word3,
      (WotsSource.publicCollect secret (stepWord key.leaf) fuel start address ends).1.val.take 48 =
        typedKeyHead seed key tag word2 word3 := by
  induction fuel with
  | zero =>
    intro start address ends oldTag old2 old3 hhead hbound
    constructor
    · simp [WotsSource.publicCollect, end_bytes_zero]
    · exact ⟨oldTag,old2,old3,by simpa only [WotsSource.publicCollect] using hhead⟩
  | succ fuel ih =>
    intro start address ends oldTag old2 old3 hhead hbound
    have hstart : start < EthLib.Cryptography.Sphincs.Constants.V := by omega
    have hs := public_step_ethlib address seed secret key ⟨start,hstart⟩ oldTag old2 old3 hhead
    simp only [WotsSource.publicCollect]
    generalize hx : WotsSource.publicStep address secret (stepWord key.leaf) start = next at hs ⊢
    obtain ⟨word2,word3,hframe⟩ := hs.2
    have hr := ih (start+1) next.2 (ends ++ next.1.val) 0#u32 word2 word3 hframe (by omega)
    have hn := congrArg Vector.toList hs.1
    rw [native_node_list] at hn
    constructor
    · rw [hr.1, List.map_append, hn, end_bytes_succ seed secret key start fuel hstart]
      simp only [List.append_assoc]
    · exact hr.2

end RustCrypto.WotsEthlib
