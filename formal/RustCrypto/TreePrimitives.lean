module
public import RustCrypto.ParentBridge
public import EthLib.Cryptography.Sphincs.Tree
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TreePrimitives
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def frame (address : Address) (seed : Node) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat) : Prop :=
  ∃ tag pair word2 word3 : U32,
    address.val.take 48 = headBytes seed (stepWord layer.toNat) (treeWord tree) tag pair word2 word3

theorem rebuild_word (word : U32) : stepWord word.val = word := by
  apply UScalar.eq_of_val_eq
  change word.val % 4294967296 = word.val
  exact Nat.mod_eq_of_lt (by scalar_tac)

/-- Tree leaf generation may enter with any prior domain, key pair and position. -/
@[step] theorem public_leaf_index_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer)
    (tree : Nat) (index : U32) (hframe : frame address seed layer tree) :
    lean_sphincs.wots.public_leaf address secret index ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.leaves EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) layer tree index.val ∧ frame out.2 seed layer tree ⦄ := by
  rcases hframe with ⟨tag,pair,word2,word3,hhead⟩
  let key : EthLib.Cryptography.Sphincs.OtsKey := ⟨layer,tree,index.val⟩
  have hh : address.val.take 48 = headBytes seed (stepWord key.layer.toNat) (treeWord key.tree)
      tag pair (stepWord word2.val) (stepWord word3.val) := by
    simpa only [key,rebuild_word] using hhead
  have hp := public_leaf_any_pair_ethlib_spec address seed secret key tag pair word2.val word3.val hh
  apply WP.spec_mono (by simpa only [key,rebuild_word] using hp)
  rintro ⟨value,next⟩ ⟨hvalue,hnext⟩
  constructor
  · simpa only [EthLib.Cryptography.Sphincs.leaves,key] using hvalue
  · rcases hnext with ⟨nextTag,next2,next3,hnext⟩
    refine ⟨nextTag,index,stepWord next2,stepWord next3,?_⟩
    simpa only [typedKeyHead,key,rebuild_word] using hnext

def zeroNode : Node := Aeneas.Std.Array.repeat 16#usize 0#u8

@[step] theorem xmss_leaf_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer)
    (tree : Nat) (index : U32) (hframe : frame address seed layer tree) :
    lean_sphincs.tree.tree_leaf address secret .Xmss index ⦃ out =>
      nativeNode out.1.1 = EthLib.Cryptography.Sphincs.leaves EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret)) layer tree index.val ∧
      out.1.2 = zeroNode ∧ frame out.2 seed layer tree ⦄ := by
  unfold lean_sphincs.tree.tree_leaf
  step with public_leaf_index_spec address seed secret layer tree index hframe
  simp only [alloy_primitives.bits.fixed.FixedBytes.ZERO]
  step*
  exact ⟨out_post,rfl,out_post1⟩

theorem native_word (word : U32) : UInt32.ofBitVec word.bv = UInt32.ofNat word.val := by
  simpa only [rebuild_word] using native_step_word word.val

theorem xmss_parent_head (seed : Node) (layer : EthLib.Cryptography.Sphincs.Layer)
    (tree : Nat) (height index : U32) :
    (headBytes seed (stepWord layer.toNat) (treeWord tree) 2#u32 0#u32 height index).map
      (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsNode layer tree height.val index.val).toList := by
  have h := canonical_prefix seed (stepWord layer.toNat) (treeWord tree) 2#u32 0#u32 height index
  have htwo : UInt32.ofBitVec (2#u32).bv = 2 := by rfl
  have hzero : UInt32.ofBitVec (0#u32).bv = UInt32.ofNat 0 := by rfl
  simpa only [native_list,native_node_list,native_step_word,native_tree_word,htwo,hzero,native_word height,native_word index,
    EthLib.Cryptography.Sphincs.adrsNode,EthLib.Cryptography.Sphincs.adrs,
    EthLib.Cryptography.Sphincs.AdrsType.code] using h

@[step] theorem xmss_parent_spec (address : Address) (seed : Node)
    (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat) (height index : U32)
    (left right : Node) (hframe : frame address seed layer tree) :
    lean_sphincs.tree.tree_parent address .Xmss height index left right ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) layer tree ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
      frame out.2 seed layer tree ⦄ := by
  rcases hframe with ⟨tag,pair,word2,word3,hhead⟩
  unfold lean_sphincs.tree.tree_parent
  simp only [lean_sphincs.tree.HYPERTREE,EthLib.Cryptography.Sphincs.nodeHash]
  step with WotsSource.domain_spec as ⟨scopedAddress,hscoped⟩
  step with RustCrypto.set_position_spec as ⟨currentAddress,hcurrent⟩
  have hd : scopedAddress.val.take 48 = headBytes seed (stepWord layer.toNat) (treeWord tree)
      2#u32 0#u32 0#u32 0#u32 := by
    rw [hscoped]
    exact domain_frame address seed (stepWord layer.toNat) (treeWord tree) tag pair word2 word3
      2#u32 0#u32 hhead
  have ha : currentAddress = positioned scopedAddress height index := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned,Aeneas.Std.Array.from_val] using hcurrent
  have hp : currentAddress.val.take 48 = headBytes seed (stepWord layer.toNat) (treeWord tree)
      2#u32 0#u32 height index := by
    rw [ha]
    exact positioned_frame scopedAddress seed (stepWord layer.toNat) (treeWord tree)
      2#u32 0#u32 0#u32 0#u32 height index hd
  have hn : (currentAddress.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsNode layer tree height.val index.val).toList := by
    rw [hp]
    exact xmss_parent_head seed layer tree height index
  step with hash_parent_ethlib_spec currentAddress left right false (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsNode layer tree height.val index.val) hn as ⟨result,hvalue,hnext⟩
  constructor
  · simpa [parentPayload] using hvalue
  · exact ⟨2#u32,0#u32,height,index,hnext.trans hp⟩

end RustCrypto.TreePrimitives
