module
public import RustCrypto.ForsForestLoop
public import RustCrypto.ForsSigningFull
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.WotsEthlib RustCrypto.AddressBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem recover_trees_spec (address : Address) (reader : Slice U8) (roots : List U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hreader : 4224 ≤ reader.val.length)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees address reader digest roots ⦃ out =>
      out.1 = some () ∧ out.2.1 = address ∧ out.2.2.1.val = reader.val.drop 4224 ∧
      nativeBytes out.2.2.2 = nativeBytes roots ++ rootsBefore reader.val digest seed idx 24 ⦄ := by
  unfold lean_sphincs.fors.recover_trees
  step with clone_array_spec address as ⟨addresses,haddresses⟩
  have hframes : ∀ j : Fin width, keyFrame (addresses[j.val]!) seed
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree := by
    intro j
    rw [haddresses j.val j.isLt]
    exact hframe
  step with forest_loop_spec reader roots addresses digest seed idx hreader hframes
    as ⟨status,remaining,nextRoots,hstatus,hremaining,hroots⟩
  exact ⟨hstatus,hremaining,hroots⟩

abbrev canonicalRecover (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) :=
  EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx
    (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))
    (Vector.ofFn (fun tree => ForsBatch.nativeOpening (openingAt bytes (176*tree.val))))

theorem canonical_recover (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) :
    canonicalRecover bytes digest seed idx =
      EthLib.Cryptography.Sphincs.forsPkFromRoots EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx
        (recoveredRoots bytes digest seed idx) := by
  unfold canonicalRecover EthLib.Cryptography.Sphincs.forsRecover
  rw [OrderedVector.ofFnInOrder_id]
  have hcb : (fun tree => EthLib.Cryptography.Sphincs.treeRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx tree
      (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[tree]
      (Vector.ofFn (fun tree => ForsBatch.nativeOpening (openingAt bytes (176*tree.val))))[tree]) =
      recovered bytes digest seed idx := by
    funext tree
    simp only [Fin.getElem_fin,Vector.getElem_ofFn]
    unfold recovered
    rfl
  rw [hcb]
  rfl

theorem roots_full (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) :
    rootsBefore bytes digest seed idx 24 =
      (EthLib.Cryptography.Sphincs.packDigests (recoveredRoots bytes digest seed idx)).data.toList := by
  unfold rootsBefore
  have h := OrderedPrefix.prefix_full (recoveredRoots bytes digest seed idx) Vector.toList
  change OrderedPrefix.collect (recoveredRoots bytes digest seed idx) _ 24 = _ at h
  rw [h]
  simp only [EthLib.Cryptography.Sphincs.packDigests,EthLib.Base.packBytes,OrderedVector.flatten_list]

/-- All source SIMD FORS recovery, including its 24-tree schedule, byte consumption and root compression. -/
@[step] theorem recover_fors_ethlib_spec (address : Address) (reader : Slice U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hreader : 4224 ≤ reader.val.length)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.fors.recover_fors address reader digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) ⦃ out =>
      out.1.map nativeNode = some (canonicalRecover reader.val digest seed idx) ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
      out.2.2.val = reader.val.drop 4224 ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx
  unfold lean_sphincs.fors.recover_fors
  simp only [lean_sphincs.fors.FORS_PUBLIC_KEY,lean_sphincs.fors.FORS_TREE]
  step with ForsPrimitives.domain_frame_spec address seed .bottom key.tree 4#u32 (stepWord key.leaf) hframe
    as ⟨publicAddress,hpublic⟩
  step with accumulator_spec publicAddress as ⟨roots,hroots⟩
  have hpublicFrame : TreePrimitives.frame publicAddress seed .bottom key.tree := ⟨4#u32,stepWord key.leaf,0#u32,0#u32,hpublic⟩
  step with ForsPrimitives.domain_frame_spec publicAddress seed .bottom key.tree 3#u32 (stepWord key.leaf) hpublicFrame
    as ⟨treeAddress,htree⟩
  have hl : key.layer = .bottom := rfl
  have htag : addressTag .forsTree = 3#u32 := rfl
  have htreeFrame : keyFrame treeAddress seed key .forsTree := by
    refine ⟨0#u32,0#u32,?_⟩
    simpa only [hl,htag] using htree
  step with recover_trees_spec treeAddress reader roots digest seed idx hreader htreeFrame
    as ⟨status,nextAddress,remaining,nextRoots,hstatus,hnext,hremaining,hrootBytes⟩
  rw [hstatus]
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok]
  have hp : nativeBytes (headBytes seed (stepWord EthLib.Cryptography.Sphincs.Layer.bottom.toNat)
      (treeWord key.tree) 4#u32 (stepWord key.leaf) 0#u32 0#u32) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsRoots idx).toList := by
    simpa only [nativeBytes,ForsSigning.asBytes] using ForsSigning.roots_head_native seed idx
  have hinput : RustCrypto.bytes nextRoots = EthLib.Cryptography.Sphincs.thInput (nativeNode seed)
      (EthLib.Cryptography.Sphincs.adrsRoots idx) (EthLib.Cryptography.Sphincs.packDigests (recoveredRoots reader.val digest seed idx)) := by
    apply ByteArray.ext
    apply _root_.Array.toList_inj.1
    rw [source_bytes_list]
    change nativeBytes nextRoots = _
    rw [hrootBytes,hroots,hpublic,hp,roots_full]
    simp only [EthLib.Cryptography.Sphincs.thInput,EthLib.Base.packBytes,ByteArray.data_append,Array.toList_append,List.append_assoc]
    rfl
  simp only [alloy_primitives.utils.Keccak256.finalize]
  step with truncate_spec (RustCrypto.digest nextRoots) as ⟨root,hroot⟩
  refine ⟨?_,?_,hremaining⟩
  · change some (nativeNode root) = some (canonicalRecover reader.val digest seed idx)
    apply congrArg some
    rw [canonical_recover]
    apply Vector.toList_inj.1
    rw [native_node_list,hroot,List.map_take,ByteBridge.digest_native]
    rw [EthLib.Cryptography.Sphincs.forsPkFromRoots,th_pure_list,hinput]
  · rw [hnext]
    exact ⟨3#u32,stepWord key.leaf,0#u32,0#u32,htree⟩

end RustCrypto.ForsForest
