module
public import RustCrypto.ForsSigningLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsSigning
open RustCrypto.AddressBridge RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.TreePrimitives RustCrypto.WotsEthlib
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

abbrev canonicalSign (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) :=
  EthLib.Cryptography.Sphincs.forsSign EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx
    (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))

theorem canonical_sign (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) :
    canonicalSign seed secret idx digest =
      ((rows seed secret idx digest).map Prod.fst,
       EthLib.Cryptography.Sphincs.forsPkFromRoots EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx
         ((rows seed secret idx digest).map Prod.snd)) := by
  unfold canonicalSign EthLib.Cryptography.Sphincs.forsSign
  rw [OrderedVector.ofFnInOrder_id]
  have hopen : (fun kappa => EthLib.Cryptography.Sphincs.treeOpen EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa
      (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[kappa]) =
      opening seed secret idx digest := by
    funext kappa
    unfold opening
    rfl
  rw [hopen]
  rfl

theorem encoded_full (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) :
    encodedPrefix seed secret idx digest 24 =
      (EthLib.Cryptography.Sphincs.encodeFors ((rows seed secret idx digest).map Prod.fst)).data.toList := by
  unfold encodedPrefix
  have h := OrderedPrefix.prefix_full (rows seed secret idx digest)
    (fun row => (EthLib.Cryptography.Sphincs.treeOpeningBytes row.1).toList)
  change OrderedPrefix.collect (rows seed secret idx digest) _ 24 = _ at h
  rw [h]
  simp only [EthLib.Cryptography.Sphincs.encodeFors,EthLib.Base.packBytes,
    OrderedVector.flatten_list,Vector.toList_map,List.flatMap_map]

theorem roots_full (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) :
    rootsPrefix seed secret idx digest 24 =
      (EthLib.Cryptography.Sphincs.packDigests ((rows seed secret idx digest).map Prod.snd)).data.toList := by
  unfold rootsPrefix
  have h := OrderedPrefix.prefix_full (rows seed secret idx digest) (fun row => row.2.toList)
  change OrderedPrefix.collect (rows seed secret idx digest) _ 24 = _ at h
  rw [h]
  simp only [EthLib.Cryptography.Sphincs.packDigests,EthLib.Base.packBytes,
    OrderedVector.flatten_list,Vector.toList_map,List.flatMap_map]

theorem roots_head_native (seed : Node) (idx : Nat) :
    asBytes (headBytes seed (stepWord (EthLib.Cryptography.Sphincs.Layer.bottom.toNat))
      (treeWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) 4#u32
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) 0#u32 0#u32) =
    (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsRoots idx).toList := by
  have hl : (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).layer = .bottom := rfl
  have hz : (0#u32).val = 0 := rfl
  simpa only [asBytes,EthLib.Cryptography.Sphincs.adrsRoots,hl,hz] using
    ForsPrimitives.typed_position_head seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx)
      4#u32 .forsRoots 0#u32 0#u32 rfl

/-- Complete source FORS signing, all 24 trees, canonical compression and exact serialization. -/
@[step] theorem sign_ethlib_spec (address : Address) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (digest : Aeneas.Std.Array U8 34#usize) (idx : Nat) (output : Slice U8)
    (hsize : 4224 ≤ output.val.length)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.fors.sign address secret digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) output ⦃ out =>
      nativeNode out.1 = (canonicalSign seed secret idx digest).2 ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
      asBytes out.2.2.val = (EthLib.Cryptography.Sphincs.encodeFors (canonicalSign seed secret idx digest).1).data.toList ++
        (asBytes output.val).drop 4224 ⦄ := by
  unfold lean_sphincs.fors.sign
  simp only [lean_sphincs.fors.FORS_PUBLIC_KEY]
  step with ForsPrimitives.domain_frame_spec address seed .bottom
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree 4#u32
    (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) hframe as ⟨scopedAddress,hhead⟩
  step with accumulator_spec scopedAddress as ⟨roots,hroots⟩
  have hscoped : TreePrimitives.frame scopedAddress seed .bottom
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree := ⟨4#u32,_,0#u32,0#u32,hhead⟩
  step with loop_spec scopedAddress seed secret digest idx output roots hsize hscoped
    as ⟨next,nextOutput,nextRoots,hnext,hbytes,hrootBytes⟩
  have hrootInput : RustCrypto.bytes nextRoots = EthLib.Cryptography.Sphincs.thInput (nativeNode seed)
      (EthLib.Cryptography.Sphincs.adrsRoots idx)
      (EthLib.Cryptography.Sphincs.packDigests ((rows seed secret idx digest).map Prod.snd)) := by
    apply ByteArray.ext
    apply _root_.Array.toList_inj.1
    rw [source_bytes_list]
    change asBytes nextRoots = _
    rw [hrootBytes,hroots,hhead,roots_head_native,roots_full]
    simp only [EthLib.Cryptography.Sphincs.thInput,EthLib.Base.packBytes,ByteArray.data_append,
      Array.toList_append,List.append_assoc]
    rfl
  simp only [alloy_primitives.utils.Keccak256.finalize]
  step with truncate_spec (RustCrypto.digest nextRoots) as ⟨root,hroot⟩
  constructor
  · rw [canonical_sign]
    apply Vector.toList_inj.1
    rw [native_node_list,hroot,List.map_take,ByteBridge.digest_native]
    rw [EthLib.Cryptography.Sphincs.forsPkFromRoots,th_pure_list,hrootInput]
  · exact ⟨hnext,by simpa only [canonical_sign,encoded_full] using hbytes⟩

end RustCrypto.ForsSigning
