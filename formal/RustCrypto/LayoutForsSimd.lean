module
public import RustCrypto.LayoutNode
public import RustCrypto.ForsForestFull
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem opening_at_get (bytes : List U8) (offset i : Nat) (hi : i < 176) :
    (ForsForest.openingAt bytes offset).val[i]! = bytes[offset+i]! := by
  rw [getElem!_pos _ i (by simp only [ForsForest.openingAt,Aeneas.Std.Array.from_val,List.length_ofFn]; exact hi)]
  simp only [ForsForest.openingAt,Aeneas.Std.Array.from_val,List.getElem_ofFn]

theorem read_node_opening (bytes : List U8) (offset level : Nat) (hlevel : level < 11) :
    ForsBatch.readNode (ForsForest.openingAt bytes offset) level = ForsRead.nodeAt bytes (offset+16*level) := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · exact (ForsBatch.readNode (ForsForest.openingAt bytes offset) level).property.trans
      (ForsRead.nodeAt bytes (offset+16*level)).property.symm
  · intro j hj hother
    have hj16 : j < 16 := by scalar_tac
    simp only [ForsBatch.readNode_eq _ _ hlevel,ForsBatch.nodeAt_val,ForsBatch.openingNode,
      List.getElem_take,List.getElem_drop,ForsForest.openingAt,Aeneas.Std.Array.from_val,List.getElem_ofFn,ForsRead.nodeAt]
    congr 1
    omega

theorem path_nodes_opening (bytes : List U8) (offset fuel level : Nat) (hlevel : fuel+level ≤ 10) :
    ForsBatch.pathNodes (ForsForest.openingAt bytes offset) fuel level = ForsRead.nodeList bytes fuel (offset+16*(level+1)) := by
  induction fuel generalizing level with
  | zero => rfl
  | succ fuel ih =>
    simp only [ForsBatch.pathNodes,ForsRead.nodeList,read_node_opening bytes offset (level+1) (by omega),
      ih (level+1) (by omega)]
    congr 1

theorem simd_opening_scalar (bytes : List U8) (offset : Nat) :
    ForsBatch.nativeOpening (ForsForest.openingAt bytes offset) = ForsRead.decodedOpening bytes offset := by
  have hs : (ForsBatch.nativeOpening (ForsForest.openingAt bytes offset)).secret =
      (ForsRead.decodedOpening bytes offset).secret := by
    have h := (ForsBatch.opening_secret (ForsForest.openingAt bytes offset)).symm
    rw [read_node_opening bytes offset 0 (by decide),Nat.mul_zero,Nat.add_zero] at h
    exact h
  have hp : (ForsBatch.nativeOpening (ForsForest.openingAt bytes offset)).path =
      (ForsRead.decodedOpening bytes offset).path := by
    apply Vector.toList_inj.1
    calc
      _ = (ForsBatch.pathNodes (ForsForest.openingAt bytes offset) 10 0).map nativeNode :=
        (ForsBatch.opening_path (ForsForest.openingAt bytes offset)).symm
      _ = (ForsRead.nodeList bytes 10 (offset+16)).map nativeNode := by
        rw [path_nodes_opening bytes offset 10 0 (by decide)]
      _ = _ := (ForsRead.nativePath_list bytes 10 (offset+16)).symm
  calc
    _ = EthLib.Cryptography.Sphincs.TreeOpening.mk
      (ForsBatch.nativeOpening (ForsForest.openingAt bytes offset)).secret
      (ForsBatch.nativeOpening (ForsForest.openingAt bytes offset)).path := rfl
    _ = EthLib.Cryptography.Sphincs.TreeOpening.mk
      (ForsRead.decodedOpening bytes offset).secret (ForsRead.decodedOpening bytes offset).path :=
      congrArg₂ EthLib.Cryptography.Sphincs.TreeOpening.mk hs hp
    _ = _ := rfl

/-- Both source FORS schedules decode exactly the same 24 openings, including their padded total models. -/
theorem simd_canonical_recover_scalar (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) :
    ForsForest.canonicalRecover bytes digest seed idx =
      EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx
        (EthLib.Cryptography.Sphincs.digestLeaves (ForsDigest.nativeDigest digest)) (ForsRead.decodedOpenings bytes) := by
  unfold ForsForest.canonicalRecover ForsRead.decodedOpenings
  have he : (Vector.ofFn (fun tree => ForsBatch.nativeOpening (ForsForest.openingAt bytes (176*tree.val)))) =
      Vector.ofFn (fun tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES => ForsRead.decodedOpening bytes (176*tree.val)) := by
    apply congrArg Vector.ofFn
    funext tree
    exact simd_opening_scalar bytes (176*tree.val)
  rw [he]

end RustCrypto.Layout
