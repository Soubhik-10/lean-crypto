module
public import RustCrypto.Hash.DomainFrame
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def nativeSeed (seed : Aeneas.Std.Array U8 32#usize) : EthLib.Cryptography.Sphincs.Seed :=
  ⟨(seed.val.map (fun b => UInt8.ofBitVec b.bv)).toArray,
    by simp [EthLib.Cryptography.Sphincs.Constants.SEED_LEN]⟩

@[simp] theorem native_seed_list (seed : Aeneas.Std.Array U8 32#usize) :
    (nativeSeed seed).toList = seed.val.map (fun b => UInt8.ofBitVec b.bv) := by rfl

theorem secret_preimage (address : Address) (secret : Aeneas.Std.Array U8 32#usize)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    RustCrypto.bytes (address.val.take 48 ++ secret.val) =
      EthLib.Cryptography.Sphincs.thInput seed adrs (EthLib.Base.packBytes (nativeSeed secret)) := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  simp_all [EthLib.Cryptography.Sphincs.thInput, EthLib.Base.packBytes,
    source_bytes_list, nativeSeed, Vector.toList, List.map_append, List.append_assoc]

@[step] theorem derive_secret_ethlib_spec (address : Address) (secret : Aeneas.Std.Array U8 32#usize)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    lean_sphincs.hash.HashContext.derive_secret address secret ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
        seed (nativeSeed secret) adrs ∧ out.2.val.take 48 = address.val.take 48 ⦄ := by
  apply WP.spec_mono (RustCrypto.derive_secret_spec address secret)
  rintro ⟨result,next⟩ ⟨hout,hnext⟩
  have hfull : address.val.setSlice! 48 secret.val = address.val.take 48 ++ secret.val := by
    simp [List.setSlice!]
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list, hout, hfull, List.map_take, ByteBridge.digest_native,
      EthLib.Cryptography.Sphincs.prf, th_pure_list, secret_preimage address secret seed adrs hprefix]
  · rw [hnext]
    simp [List.setSlice!, List.take_of_length_le]

/-- The actual WOTS chain start uses EthLib's PRF address and resets the chain domain. -/
@[step] theorem chain_start_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) (oldTag : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = typedKeyHead seed key oldTag old2 old3) :
    lean_sphincs.wots.chain_start address secret (stepWord key.leaf) (stepWord chain.val) ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (nativeSeed secret) (EthLib.Cryptography.Sphincs.adrsPrf key chain) ∧
      out.2.val.take 48 = keyHead seed key 0 0 ⦄ := by
  unfold lean_sphincs.wots.chain_start
  simp only [lean_sphincs.wots.WOTS_PRF, lean_sphincs.wots.WOTS_CHAIN]
  step with WotsSource.domain_spec
  step
  have hzero : stepWord 0 = 0#u32 := by
    apply UScalar.eq_of_val_eq
    rfl
  have hd : address1.val.take 48 = typedKeyHead seed key 5#u32 0 0 := by
    rw [address1_post]
    simpa only [typedKeyHead, hzero] using
      domain_frame address seed (stepWord key.layer.toNat) (treeWord key.tree) oldTag
        (stepWord key.leaf) (stepWord old2) (stepWord old3) 5#u32 (stepWord key.leaf) hhead
  have ha : address2 = positioned address1 (stepWord chain.val) 0#u32 := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned, Aeneas.Std.Array.from_val] using address2_post
  have hp : address2.val.take 48 = typedKeyHead seed key 5#u32 chain.val 0 := by
    rw [ha]
    simpa only [typedKeyHead, hzero] using
      positioned_frame address1 seed (stepWord key.layer.toNat) (treeWord key.tree) 5#u32
        (stepWord key.leaf) (stepWord 0) (stepWord 0) (stepWord chain.val) 0#u32 hd
  have hn : (address2.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsPrf key chain).toList := by
    rw [hp]
    exact prf_head_native seed key chain
  step with derive_secret_ethlib_spec address2 secret (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsPrf key chain) hn
  step with WotsSource.domain_spec
  constructor
  · exact secret_post
  · rw [address4_post]
    have hh : address3.val.take 48 = typedKeyHead seed key 5#u32 chain.val 0 := by
      rw [secret_post1, hp]
    simpa only [typedKeyHead, keyHead, hzero] using
      domain_frame address3 seed (stepWord key.layer.toNat) (treeWord key.tree) 5#u32
        (stepWord key.leaf) (stepWord chain.val) (stepWord 0) 0#u32 (stepWord key.leaf) hh

end RustCrypto.WotsEthlib
