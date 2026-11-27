module
public import RustCrypto.Signing.Full.Failure
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def selectPath (secret : Aeneas.Std.Array U8 32#usize) (cache : lean_sphincs.tree.TopTree)
    (address : Address) (node : Node) (output : Slice U8) (stage : Usize) (height leaf : U32) :
    Result (Address × Node × Slice U8 × Aeneas.Std.Array Node 10#usize) := do
  let fb ← alloy_primitives.bits.fixed.FixedBytes.ZERO 16#usize
  let path := Aeneas.Std.Array.repeat 10#usize fb
  let s3 ← lift (Aeneas.Std.Array.to_slice lean_sphincs.params.LAYER_HEIGHTS)
  let i8 ← Slice.len s3 - 1#usize
  if stage = i8 then
    let path2 ← lean_sphincs.tree.TopTree.path cache leaf
    ok (address,node,output,path2)
  else
    let i9 ← lift (UScalar.cast .Usize height)
    let (s4,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Node)) path { «end» := i9 }
    let (node2,address4,s5) ← lean_sphincs.tree.build_xmss address secret height leaf s4
    ok (address4,node2,output,back s5)

theorem key_top_tree (index : Nat) (hindex : index < 67108864) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .top index).tree = 0 := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,Nat.shiftRight_eq_div_pow,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Layer.below,
    EthLib.Cryptography.Sphincs.Constants.TOP_HEIGHT]
  exact Nat.div_eq_of_lt hindex

theorem built_root_canonical (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) :
    (EthLib.Cryptography.Sphincs.buildTree EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
      key.layer key.tree).value = EthLib.Cryptography.Sphincs.treeRoot EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
      key.layer key.tree := by
  simpa only [EthLib.Cryptography.Sphincs.buildTree,EthLib.Cryptography.Sphincs.treeRoot,
    EthLib.Cryptography.Merkle.root,EthLib.Cryptography.Merkle.node] using
    RustCrypto.MerklePath.build_value
      (EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key.layer key.tree)
      (EthLib.Cryptography.Sphincs.leaves EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) key.layer key.tree)
      key.layer.height 0

@[step] theorem select_path_spec (secret : Aeneas.Std.Array U8 32#usize) (cache : lean_sphincs.tree.TopTree)
    (address : Address) (node seed : Node) (output : Slice U8) (stage : Usize)
    (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat)
    (hindex : index < 67108864) (hstage : stage.val = layer.toNat)
    (hvalid : TopCache.validThrough cache.nodes seed secret 10)
    (hframe : TreePrimitives.frame address seed layer (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree) :
    selectPath secret cache address node output stage (stepWord layer.height)
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf) ⦃ out =>
      TreePrimitives.frame out.1 seed layer (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      nativeNode out.2.1 = nextMessage seed secret (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) (nativeNode node) ∧
      out.2.2.1 = output ∧
      (out.2.2.2.val.take layer.height).map nativeNode =
        (pathValues seed secret (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index)).toList ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
  have hheight : layer.height ≤ 10 := layer_height_bound layer
  have hleaf : key.leaf < 2^layer.height := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hleafBound : key.leaf < 1024 := LayerInput.key_leaf_bound layer index
  have hlval : (stepWord key.leaf).val = key.leaf := RustCrypto.ClimbBridge.step_word_value key.leaf (by omega)
  unfold selectPath
  simp only [alloy_primitives.bits.fixed.FixedBytes.ZERO,lift,bind_ok]
  step as ⟨last,hlast⟩
  have hv : last.val = 2 := by
    simp [Slice.len,Aeneas.Std.Array.to_slice,Slice.from_val,RustIndex.layer_heights_eq] at hlast
    scalar_tac
  by_cases htop : layer = .top
  · have hs : stage = last := by apply UScalar.eq_of_val_eq; rw [hstage,hv,htop]; rfl
    rw [ite_eq_left hs]
    have hb : (stepWord key.leaf).val < 1024 := by rw [hlval]; exact LayerInput.key_leaf_bound layer index
    step with TopCache.path_ethlib_spec cache (stepWord key.leaf) seed secret hb hvalid as ⟨path,hpath⟩
    refine ⟨hframe,?_,?_⟩
    · unfold nextMessage
      simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,htop,ite_true]
    · have ht : key.tree = 0 := by simpa only [key,htop] using key_top_tree index hindex
      have hp : key.layer = .top := htop
      have hlen : path.val.length ≤ layer.height := by rw [htop]; exact Nat.le_of_eq path.property
      rw [List.take_of_length_le hlen]
      unfold pathValues
      change path.val.map nativeNode = (EthLib.Cryptography.Sphincs.path EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
        key.layer key.tree key.leaf).toList
      rw [hp,ht]
      change path.val.map nativeNode = (EthLib.Cryptography.Sphincs.path EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
        .top 0 (stepWord key.leaf).val).toList at hpath
      rw [hlval] at hpath
      exact hpath
  · have hs : stage ≠ last := by
      intro he
      have hn : layer.toNat = 2 := by rw [←hstage,he,hv]
      cases layer <;> simp_all [EthLib.Cryptography.Sphincs.Layer.toNat]
    rw [ite_eq_right hs]
    have hcast : (UScalar.cast .Usize (stepWord layer.height)).val = layer.height := by
      rw [UScalar.cast_val_eq,LayerInput.height_word_val]
      exact Nat.mod_eq_of_lt (by have hp := System.Platform.numBits_eq; cases hp <;> scalar_tac)
    step as ⟨path,back,hpath,hpathLen,hback⟩
    have hpLen : path.val.length = (stepWord layer.height).val := by
      dsimp only [Slice.length] at hpathLen
      rw [hcast] at hpathLen
      rw [LayerInput.height_word_val]
      exact hpathLen
    step with BuildRoot.build_xmss_opening_ethlib_spec address seed secret layer key.tree (stepWord layer.height)
      (stepWord key.leaf) path (LayerInput.height_word_val layer) (by rw [hlval,LayerInput.height_word_val]; exact hleaf) hpLen hframe
      as ⟨root,nextAddress,newPath,hroot,hnewPath,hnextFrame⟩
    refine ⟨hnextFrame,?_,?_⟩
    · unfold nextMessage
      have hk : (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).layer = layer := rfl
      rw [hk,ite_eq_right htop]
      exact hroot.trans (built_root_canonical seed secret key)
    · rw [hback]
      have hsize : newPath.val.length = layer.height := by
        have h := congrArg List.length hnewPath
        simpa only [List.length_map,Vector.length_toList] using h
      have hroom : 0+newPath.val.length ≤ (Aeneas.Std.Array.repeat 10#usize (Aeneas.Std.Array.repeat 16#usize 0#u8)).val.length := by
        simp only [Aeneas.Std.Array.repeat_val,List.length_replicate]
        change 0+newPath.val.length ≤ 10
        omega
      have hp := overwrite_prefix (Aeneas.Std.Array.repeat 10#usize (Aeneas.Std.Array.repeat 16#usize 0#u8)).val newPath.val 0 hroom
      simp only [Nat.zero_add,List.take_zero,List.nil_append,hsize] at hp
      rw [hp,hnewPath,hlval]
      exact built_path_canonical seed secret key hleaf

end RustCrypto.FullSign
