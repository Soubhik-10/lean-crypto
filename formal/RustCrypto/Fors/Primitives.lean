module
public import RustCrypto.Fors.Positions
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsPrimitives
open RustCrypto.WotsEthlib RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TreePrimitives
open RustCrypto.TweakableBridge RustCrypto.ForsPositions
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem typed_position_head (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (tag : U32) (kind : EthLib.Cryptography.Sphincs.AdrsType) (height index : U32)
    (htag : UInt32.ofBitVec tag.bv = kind.code) :
    (headBytes seed (stepWord key.layer.toNat) (treeWord key.tree) tag
      (stepWord key.leaf) height index).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.keyAdrs kind key height.val index.val).toList := by
  have h := canonical_prefix seed (stepWord key.layer.toNat) (treeWord key.tree) tag
    (stepWord key.leaf) height index
  simpa only [native_list,native_node_list,native_step_word,native_tree_word,htag,native_word height,
    native_word index,EthLib.Cryptography.Sphincs.keyAdrs,EthLib.Cryptography.Sphincs.adrs] using h

@[step] theorem domain_frame_spec (address : Address) (seed : Node)
    (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat) (tag pair : U32)
    (hframe : frame address seed layer tree) :
    lean_sphincs.hash.HashContext.set_domain address tag pair ⦃ out =>
      out.val.take 48 = headBytes seed (stepWord layer.toNat) (treeWord tree) tag pair 0#u32 0#u32 ⦄ := by
  rcases hframe with ⟨oldTag,oldPair,old2,old3,hhead⟩
  apply WP.spec_mono (WotsSource.domain_spec address tag pair)
  intro next hnext
  rw [hnext]
  exact domain_frame address seed (stepWord layer.toNat) (treeWord tree)
    oldTag oldPair old2 old3 tag pair hhead

@[step] theorem position_frame_spec (address : Address) (seed : Node)
    (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat) (tag pair old2 old3 height index : U32)
    (hhead : address.val.take 48 = headBytes seed (stepWord layer.toNat) (treeWord tree) tag pair old2 old3) :
    lean_sphincs.hash.HashContext.set_position address height index ⦃ out =>
      out.val.take 48 = headBytes seed (stepWord layer.toNat) (treeWord tree) tag pair height index ⦄ := by
  apply WP.spec_mono (RustCrypto.set_position_spec address height index)
  intro next hnext
  have heq : next = positioned address height index := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned,Aeneas.Std.Array.from_val] using hnext
  rw [heq]
  exact positioned_frame address seed (stepWord layer.toNat) (treeWord tree) tag pair old2 old3 height index hhead

@[step] theorem fors_parent_spec (address : Address) (seed : Node) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (height index : U32)
    (left right : Node) (hheight : height.val ≤ 10) (hindex : index.val < 2^(10-height.val))
    (hframe : frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.tree_parent address
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf))
      height index left right ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) idx kappa ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
      frame out.2 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx
  have hl : key.layer = .bottom := rfl
  have hz : (0#u32).val = 0 := rfl
  have hk : (stepWord kappa.val).val = kappa.val := by
    change kappa.val % 4294967296 = kappa.val
    have hb := kappa.isLt
    exact Nat.mod_eq_of_lt (by
      have : kappa.val < 24 := hb
      omega)
  have hkl : (stepWord kappa.val).val < 24 := by
    rw [hk]
    exact kappa.isLt
  unfold lean_sphincs.tree.tree_parent
  simp only [lean_sphincs.tree.FORS_TREE,lean_sphincs.params.FORS_HEIGHT]
  step with domain_frame_spec address seed .bottom key.tree 3#u32 (stepWord key.leaf) hframe
    as ⟨scopedAddress,hscoped⟩
  step as ⟨remaining,hremaining⟩
  step with shift_index_spec (stepWord kappa.val) remaining hkl (by scalar_tac)
    as ⟨shifted,hshifted⟩
  have hj : (shifted ||| index).val = EthLib.Cryptography.Sphincs.forsTreeIndex kappa height.val index.val := by
    rw [joined_index shifted (stepWord kappa.val) remaining index hshifted (by simpa [hremaining] using hindex),hk]
    simp only [EthLib.Cryptography.Sphincs.forsTreeIndex,EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT,hremaining]
  step as ⟨global,hglobal⟩
  have hg : global = shifted ||| index := UScalar.eq_of_val_eq hglobal
  subst global
  step with position_frame_spec scopedAddress seed .bottom key.tree 3#u32 (stepWord key.leaf)
    0#u32 0#u32 height (shifted ||| index) hscoped as ⟨currentAddress,hcurrent⟩
  have hn : (currentAddress.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsFors idx height.val
        (EthLib.Cryptography.Sphincs.forsTreeIndex kappa height.val index.val)).toList := by
    rw [hcurrent]
    simpa only [EthLib.Cryptography.Sphincs.adrsFors,hl,hz,hj] using
      typed_position_head seed key 3#u32 .forsTree height (shifted ||| index) rfl
  step with hash_parent_ethlib_spec currentAddress left right false (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsFors idx height.val
      (EthLib.Cryptography.Sphincs.forsTreeIndex kappa height.val index.val)) hn as ⟨result,hvalue,hnext⟩
  constructor
  · simpa only [EthLib.Cryptography.Sphincs.forsNodeHash,parentPayload,Bool.false_eq_true,reduceIte] using hvalue
  · exact ⟨3#u32,stepWord key.leaf,height,shifted ||| index,hnext.trans hcurrent⟩

@[step] theorem fors_leaf_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (index : U32)
    (hindex : index.val < 1024)
    (hframe : frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.tree_leaf address secret
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)) index ⦃ out =>
      nativeNode out.1.1 = EthLib.Cryptography.Sphincs.forsLeaves EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) idx kappa index.val ∧
      nativeNode out.1.2 = EthLib.Cryptography.Sphincs.forsSecret
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) idx kappa index.val ∧
      frame out.2 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx
  have hl : key.layer = .bottom := rfl
  have hz : (0#u32).val = 0 := rfl
  have hk : (stepWord kappa.val).val = kappa.val := by
    change kappa.val % 4294967296 = kappa.val
    have hb := kappa.isLt
    exact Nat.mod_eq_of_lt (by
      have : kappa.val < 24 := hb
      omega)
  have hkl : (stepWord kappa.val).val < 24 := by
    rw [hk]
    exact kappa.isLt
  unfold lean_sphincs.tree.tree_leaf
  simp only [lean_sphincs.tree.FORS_TREE,lean_sphincs.tree.FORS_PRF,lean_sphincs.params.FORS_HEIGHT]
  step with domain_frame_spec address seed .bottom key.tree 6#u32 (stepWord key.leaf) hframe
    as ⟨prfAddress,hprf⟩
  step with shift_index_spec (stepWord kappa.val) 10#u32 hkl (by decide) as ⟨shifted,hshifted⟩
  have hj : (shifted ||| index).val = EthLib.Cryptography.Sphincs.forsTreeIndex kappa 0 index.val := by
    rw [joined_index shifted (stepWord kappa.val) 10#u32 index hshifted hindex,hk]
    rfl
  step as ⟨global,hglobal⟩
  have hg : global = shifted ||| index := UScalar.eq_of_val_eq hglobal
  subst global
  step with position_frame_spec prfAddress seed .bottom key.tree 6#u32 (stepWord key.leaf)
    0#u32 0#u32 0#u32 (shifted ||| index) hprf as ⟨secretAddress,hsecret⟩
  have hsn : (secretAddress.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsFprf idx
        (EthLib.Cryptography.Sphincs.forsTreeIndex kappa 0 index.val)).toList := by
    rw [hsecret]
    simpa only [EthLib.Cryptography.Sphincs.adrsFprf,hl,hz,hj] using
      typed_position_head seed key 6#u32 .forsPrf 0#u32 (shifted ||| index) rfl
  step with derive_secret_ethlib_spec secretAddress secret (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsFprf idx (EthLib.Cryptography.Sphincs.forsTreeIndex kappa 0 index.val)) hsn
    as ⟨derived,hashedAddress,hderived,hhashed⟩
  have hf : frame hashedAddress seed .bottom key.tree :=
    ⟨6#u32,stepWord key.leaf,0#u32,shifted ||| index,hhashed.trans hsecret⟩
  step with domain_frame_spec hashedAddress seed .bottom key.tree 3#u32 (stepWord key.leaf) hf
    as ⟨leafAddress,hleaf⟩
  step as ⟨global,hglobal⟩
  have hg : global = shifted ||| index := UScalar.eq_of_val_eq hglobal
  subst global
  step with position_frame_spec leafAddress seed .bottom key.tree 3#u32 (stepWord key.leaf)
    0#u32 0#u32 0#u32 (shifted ||| index) hleaf as ⟨nodeAddress,hnode⟩
  have hnn : (nodeAddress.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsFors idx 0
        (EthLib.Cryptography.Sphincs.forsTreeIndex kappa 0 index.val)).toList := by
    rw [hnode]
    simpa only [EthLib.Cryptography.Sphincs.adrsFors,hl,hz,hj] using
      typed_position_head seed key 3#u32 .forsTree 0#u32 (shifted ||| index) rfl
  step with hash_node_ethlib_spec nodeAddress derived (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsFors idx 0 (EthLib.Cryptography.Sphincs.forsTreeIndex kappa 0 index.val)) hnn
    as ⟨value,nextAddress,hvalue,hnext⟩
  refine ⟨?_,hderived,3#u32,stepWord key.leaf,0#u32,shifted ||| index,hnext.trans hnode⟩
  simpa only [EthLib.Cryptography.Sphincs.forsLeaves,EthLib.Cryptography.Sphincs.forsLeafHash,
    EthLib.Cryptography.Sphincs.forsSecret,Id.run,Bind.bind,Pure.pure,hderived] using hvalue

end RustCrypto.ForsPrimitives
