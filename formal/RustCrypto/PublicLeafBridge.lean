module
public import RustCrypto.WotsPublic
public import RustCrypto.VectorFlatten
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem vector_ofFn_get {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  change (Vector.ofFn f)[i.val]'i.isLt = f i
  exact Vector.getElem_ofFn i.isLt

theorem canonical_public_leaf (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) :
    EthLib.Cryptography.Sphincs.otsPublicLeaf EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) key =
    EthLib.Cryptography.Sphincs.otsLeafHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key
      (Vector.ofFn (publicEnd seed secret key)) := by
  unfold EthLib.Cryptography.Sphincs.otsPublicLeaf EthLib.Cryptography.Sphincs.chainStarts
  simp only [OrderedVector.ofFnInOrder_id]
  apply congrArg (EthLib.Cryptography.Sphincs.otsLeafHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key)
  apply congrArg Vector.ofFn
  funext chain
  simp only [vector_ofFn_get, publicEnd, EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH, Nat.reduceSub]

theorem pk_head_native (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) :
    (typedKeyHead seed key 1#u32 0 0).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsPk key).toList := by
  have h := canonical_prefix seed (stepWord key.layer.toNat) (treeWord key.tree) 1#u32
    (stepWord key.leaf) (stepWord 0) (stepWord 0)
  have hone : UInt32.ofBitVec (1#u32).bv = 1 := by rfl
  simpa only [typedKeyHead, native_list, native_node_list, native_step_word, native_tree_word, hone,
    EthLib.Cryptography.Sphincs.adrsPk, EthLib.Cryptography.Sphincs.keyAdrs,
    EthLib.Cryptography.Sphincs.adrs, EthLib.Cryptography.Sphincs.AdrsType.code] using h

theorem complete_end_bytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) :
    endBytes seed secret key 0 64 =
      (EthLib.Cryptography.Sphincs.packDigests (Vector.ofFn (publicEnd seed secret key))).data.toList := by
  simp only [EthLib.Cryptography.Sphincs.packDigests, EthLib.Base.packBytes,
    OrderedVector.flatten_list, Vector.toList_ofFn]
  unfold endBytes
  simp only [List.drop_zero]
  have hlen : (List.ofFn (publicEnd seed secret key)).length = EthLib.Cryptography.Sphincs.Constants.V :=
    List.length_ofFn
  have hle : (List.ofFn (publicEnd seed secret key)).length ≤ 64 :=
    Nat.le_of_eq (hlen.trans (by rfl))
  rw [List.take_of_length_le hle]

/-- Complete source WOTS public-key generation refines EthLib, including canonical addressed PRFs. -/
@[step] theorem public_leaf_any_pair_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (oldTag oldPair : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = headBytes seed (stepWord key.layer.toNat) (treeWord key.tree)
      oldTag oldPair (stepWord old2) (stepWord old3)) :
    lean_sphincs.wots.public_leaf address secret (stepWord key.leaf) ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.otsPublicLeaf EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) key ∧
      ∃ tag word2 word3, out.2.val.take 48 = typedKeyHead seed key tag word2 word3 ⦄ := by
  let initial := WotsSource.domain address 1#u32 (stepWord key.leaf)
  let collected := WotsSource.publicCollect secret (stepWord key.leaf) 64 0 initial (initial.val.take 48)
  have hzero : stepWord 0 = 0#u32 := by
    apply UScalar.eq_of_val_eq
    rfl
  have hi : initial.val.take 48 = typedKeyHead seed key 1#u32 0 0 := by
    simpa only [initial, typedKeyHead, hzero] using
      domain_frame address seed (stepWord key.layer.toNat) (treeWord key.tree) oldTag
        oldPair (stepWord old2) (stepWord old3) 1#u32 (stepWord key.leaf) hhead
  have hc := collect_ethlib seed secret key 64 0 initial (initial.val.take 48) 1#u32 0 0 hi
    (Nat.le_of_eq (by rfl))
  have hp : (initial.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsPk key).toList := by
    rw [hi]
    exact pk_head_native seed key
  have hb : RustCrypto.bytes collected.2 = EthLib.Cryptography.Sphincs.thInput (nativeNode seed)
      (EthLib.Cryptography.Sphincs.adrsPk key)
      (EthLib.Cryptography.Sphincs.packDigests (Vector.ofFn (publicEnd seed secret key))) := by
    apply ByteArray.ext
    apply _root_.Array.toList_inj.1
    rw [source_bytes_list, hc.1, hp, complete_end_bytes]
    simp [EthLib.Cryptography.Sphincs.thInput, EthLib.Base.packBytes, Vector.toList, List.append_assoc]
  apply WP.spec_mono (WotsSource.public_leaf_spec address secret (stepWord key.leaf))
  intro out hout
  rw [hout]
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list]
    simp only [WotsSource.publicLeaf, Aeneas.Std.Array.from_val]
    rw [List.map_take, ByteBridge.digest_native, canonical_public_leaf,
      EthLib.Cryptography.Sphincs.otsLeafHash, th_pure_list]
    exact congrArg (fun input => (EthLib.Cryptography.Hash.Keccak.keccak256 input).toList.take 16) hb
  · simpa only [WotsSource.publicLeaf] using hc.2


@[step] theorem public_leaf_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (oldTag : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = typedKeyHead seed key oldTag old2 old3) :
    lean_sphincs.wots.public_leaf address secret (stepWord key.leaf) ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.otsPublicLeaf EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) key ∧
      ∃ tag word2 word3, out.2.val.take 48 = typedKeyHead seed key tag word2 word3 ⦄ := by
  exact public_leaf_any_pair_ethlib_spec address seed secret key oldTag (stepWord key.leaf) old2 old3 hhead

end RustCrypto.WotsEthlib
