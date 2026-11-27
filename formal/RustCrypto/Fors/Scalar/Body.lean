module
public import RustCrypto.Fors.Scalar.Bytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsScalar
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def treeAt (index : Usize) (hindex : index.val < 24) : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES := ⟨index.val,hindex⟩

def leafAt (digest : Aeneas.Std.Array U8 34#usize) (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) :=
  (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[tree]

theorem leafAt_val (digest : Aeneas.Std.Array U8 34#usize) (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) :
    (leafAt digest tree).val = EthLib.Cryptography.Sphincs.msbField (RustCrypto.ForsDigest.nativeDigest digest) (10*tree.val) 10 := by
  simp only [leafAt,EthLib.Cryptography.Sphincs.digestLeaves,Fin.getElem_fin,Vector.getElem_ofFn]
  rfl

@[step] theorem body_spec (address : Address) (reader : Slice U8) (roots : List U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) (index : Usize)
    (hindex : index.val < 24) (hreader : 176 ≤ reader.val.length)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop.body digest address reader roots index ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextReader,nextRoots,nextIndex) =>
          nextIndex.val = index.val+1 ∧ nextReader.val = reader.val.drop 176 ∧
          keyFrame nextAddress seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ∧
          ∃ root : Node, nativeNode root = EthLib.Cryptography.Sphincs.treeRecover EthLib.Cryptography.Sphincs.hashId
            (nativeNode seed) idx (treeAt index hindex) (leafAt digest (treeAt index hindex)) (decodedOpening reader.val 0) ∧
            nextRoots = roots ++ root.val ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx
  let tree := treeAt index hindex
  let leaf := leafAt digest tree
  unfold lean_sphincs.fors.recover_trees_loop.body
  have hrun : index < lean_sphincs.params.FORS_TREES := by
    simp only [lean_sphincs.params.FORS_TREES]
    scalar_tac
  simp only [ite_eq_left hrun]
  step with RustCrypto.ForsDigest.leaf_position_ethlib_spec digest index hindex as ⟨position,hposition⟩
  have hp : position.val = EthLib.Cryptography.Sphincs.forsTreeIndex tree 0 leaf.val := by
    simpa only [tree,leaf,treeAt,leafAt_val,EthLib.Cryptography.Sphincs.forsTreeIndex,
      EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT,Nat.sub_zero,Nat.reducePow] using hposition
  rcases hframe with ⟨old2,old3,hhead⟩
  have hl : key.layer = .bottom := rfl
  have htag : addressTag .forsTree = 3#u32 := rfl
  have hh : address.val.take 48 = RustCrypto.AddressBridge.headBytes seed (stepWord key.layer.toNat)
      (treeWord key.tree) 3#u32 (stepWord key.leaf) old2 old3 := by simpa only [htag] using hhead
  step with ForsPrimitives.position_frame_spec address seed key.layer key.tree 3#u32 (stepWord key.leaf)
    old2 old3 0#u32 position hh as ⟨positionedAddress,hpositioned⟩
  rw [RustParser.take_success 16#usize reader (by scalar_tac)]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  have hsecret : RustParser.readPrefix 16#usize reader (by scalar_tac) = ForsRead.nodeAt reader.val 0 := by
    apply Aeneas.Std.Array.ext
    rw [ForsRead.nodeAt_val reader.val 0 (by omega)]
    have h16 : (16#usize).val = 16 := rfl
    simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,List.drop_zero,h16]
  rw [hsecret]
  have hz : (0#u32).val = 0 := rfl
  have hn : (positionedAddress.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsFors idx 0
        (EthLib.Cryptography.Sphincs.forsTreeIndex tree 0 leaf.val)).toList := by
    rw [hpositioned]
    simpa only [EthLib.Cryptography.Sphincs.adrsFors,hz,hp] using
      ForsPrimitives.typed_position_head seed key 3#u32 .forsTree 0#u32 position rfl
  step with hash_node_ethlib_spec positionedAddress (ForsRead.nodeAt reader.val 0) (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsFors idx 0 (EthLib.Cryptography.Sphincs.forsTreeIndex tree 0 leaf.val)) hn
    as ⟨node,hashedAddress,hnode,hhashed⟩
  have hhashedFrame : keyFrame hashedAddress seed key .forsTree := by
    refine ⟨0#u32,position,?_⟩
    simpa only [htag] using hhashed.trans hpositioned
  have hpathReader : (RustParser.readSuffix 16#usize reader).val =
      nodesBytes (nodeList reader.val 10 16) ++ reader.val.drop 176 := by
    rw [serialized_nodes reader.val 10 16 (by omega)]
    have h16 : (16#usize).val = 16 := rfl
    simp only [RustParser.readSuffix,Slice.from_val,h16]
    have h := List.take_append_drop 160 (reader.val.drop 16)
    simpa only [List.drop_drop,Nat.reduceAdd] using h.symm
  simp only [lean_sphincs.params.FORS_HEIGHT]
  step with RustCrypto.ForsClimb.climb_fors_ethlib_spec hashedAddress (RustParser.readSuffix 16#usize reader)
    position node seed idx tree leaf.val (nodeList reader.val 10 16) (reader.val.drop 176)
    (nodeList_length _ _ _) hp hhashedFrame hpathReader
    as ⟨rootOption,nextAddress,remaining,hroot,hremaining,hnext⟩
  cases rootOption with
  | none =>
    simp only [Option.map_none] at hroot
    cases hroot
  | some root =>
    simp only [Option.map_some,Option.some.injEq] at hroot
    simp only [alloy_primitives.utils.Keccak256.update,alloy_primitives.bits.fixed.FixedBytes.Insts.CoreConvertAsRefSliceU8.as_ref,
      Aeneas.Std.Array.to_slice]
    step as ⟨nextIndex,hnextIndex⟩
    refine ⟨?_,hremaining,hnext,root,?_,?_⟩
    · have h1 : (1#usize).val = 1 := rfl
      simpa only [h1] using hnextIndex
    · rw [hroot]
      simp only [EthLib.Cryptography.Sphincs.treeRecover,decodedOpening,Nat.zero_add,Bind.bind,
        EthLib.Cryptography.Sphincs.forsLeafHash,hnode]
      exact congrArg (EthLib.Cryptography.Merkle.climb _ _ _) (nativePath_list reader.val 10 16).symm
    · simp only [Slice.from_val]

end RustCrypto.ForsScalar
