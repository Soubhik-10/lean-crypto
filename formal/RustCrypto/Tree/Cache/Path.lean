module
public import RustCrypto.Tree.Cache.PathIndex
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem path_closure_spec (cache : lean_sphincs.tree.TopTree) (leaf : U32) (level : Usize)
    (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (hleaf : leaf.val < 1024) (hlevel : level.val < 10)
    (hvalid : validThrough cache.nodes seed secret 10) :
    lean_sphincs.tree.TopTree.path.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut (cache,leaf) level
      ⦃ out => nativeNode out.1 = value seed secret level.val ((leaf.val/2^level.val) ^^^ 1) ∧ out.2 = (cache,leaf) ⦄ := by
  unfold lean_sphincs.tree.TopTree.path.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFixedBytes16.call_mut
  have hbits := System.Platform.le_numBits
  step as ⟨leafIndex,hleafIndex⟩
  have hl : leafIndex.val = leaf.val := by scalar_tac
  step with top_leaves_spec as ⟨limit,hlimit⟩
  rw [hlimit]
  step as ⟨sum,hsum⟩
  have hv : sum.val = 1024+leaf.val := by scalar_tac
  step as ⟨shifted,hshifted⟩
  have hs : shifted.val = (1024+leaf.val)/2^level.val := by
    rw [hshifted,hv,Nat.shiftRight_eq_div_pow]
  step as ⟨index,hindex⟩
  have hx : index.val = width level.val+((leaf.val/2^level.val) ^^^ 1) := by
    rw [hindex,UScalar.val_xor,show (1#usize).val = 1 from rfl,hs,heap_path_index leaf.val level.val hlevel]
  have hsb := sibling_bound leaf.val level.val hleaf hlevel
  have hw := width_bounded level.val
  have hib : index.val < 2048 := by omega
  step as ⟨node,hnode⟩
  have hn : node = cache.nodes[index.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos cache.nodes.val index.val (by scalar_tac)]
    exact hnode
  refine ⟨?_,rfl⟩
  rw [hn,hx]
  exact hvalid level.val (by omega) ((leaf.val/2^level.val) ^^^ 1) hsb

@[step] theorem path_array_spec (cache : lean_sphincs.tree.TopTree) (leaf : U32)
    (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (hleaf : leaf.val < 1024)
    (hvalid : validThrough cache.nodes seed secret 10) :
    lean_sphincs.tree.TopTree.path cache leaf ⦃ out =>
      ∀ j < 10, nativeNode (out[j]!) = value seed secret j ((leaf.val/2^j) ^^^ 1) ⦄ := by
  unfold lean_sphincs.tree.TopTree.path
  apply core.array.from_fn.spec_stateless_getElem! _ _ _ (fun level (node : Node) =>
    nativeNode node = value seed secret level ((leaf.val/2^level) ^^^ 1))
  intro level hlevel
  exact path_closure_spec cache leaf level seed secret hleaf hlevel hvalid

/-- Every cached authentication path is exactly EthLib's canonical sibling vector. -/
@[step] theorem path_ethlib_spec (cache : lean_sphincs.tree.TopTree) (leaf : U32)
    (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (hleaf : leaf.val < 1024)
    (hvalid : validThrough cache.nodes seed secret 10) :
    lean_sphincs.tree.TopTree.path cache leaf ⦃ out => out.val.map nativeNode =
      (EthLib.Cryptography.Sphincs.path EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
        .top 0 leaf.val).toList ⦄ := by
  apply WP.spec_mono (path_array_spec cache leaf seed secret hleaf hvalid)
  intro path hpath
  simp only [EthLib.Cryptography.Sphincs.path,EthLib.Cryptography.Merkle.path,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.TOP_HEIGHT,
    RustCrypto.MerklePath.siblings_list]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn]
    exact path.property
  · intro j hj hother
    have hj10 : j < 10 := by scalar_tac
    rw [List.getElem_map,List.getElem_ofFn]
    have h := hpath j hj10
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos path.val j (by scalar_tac)] at h
    unfold value at h
    simpa only [EthLib.Cryptography.Sphincs.node,EthLib.Cryptography.Merkle.node,Nat.zero_add] using h

end RustCrypto.TopCache
