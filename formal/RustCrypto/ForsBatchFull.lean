module
public import RustCrypto.ForsBatchLeaf
public import RustCrypto.ForsOpeningBytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

/-- Complete source SIMD FORS recovery matches EthLib for arbitrary serialized openings in every lane. -/
@[step] theorem recover_batch_ethlib_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize) (seed : Node) (idx : Nat)
    (trees : Fin 2 → Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES)
    (leaves : Fin 2 → Fin (2^EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT))
    (hpositions : ∀ j : Fin 2, (positions[j.val]!).val =
      EthLib.Cryptography.Sphincs.forsTreeIndex (trees j) 0 (leaves j).val)
    (hframes : ∀ j : Fin 2, keyFrame (addresses[j.val]!) seed
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_batch addresses openings positions ⦃ out =>
      ∀ j : Fin 2,
        nativeNode (out.1[j.val]!) = EthLib.Cryptography.Sphincs.treeRecover EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) idx (trees j) (leaves j) (nativeOpening (openings[j.val]!)) ∧
        keyFrame (out.2[j.val]!) seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ⦄ := by
  apply WP.spec_mono (recover_batch_spec addresses openings positions)
  intro out hout j
  let start := leafStep (addresses[j.val]!) (openings[j.val]!) (positions[j.val]!)
  have hs := leaf_step_native (addresses[j.val]!) (openings[j.val]!) (positions[j.val]!) seed
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) (hframes j)
  have hw := walk_native (openings[j.val]!) 10 0 (positions[j.val]!) start.1 start.2 seed
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree (by decide) hs.2
  have hleaf : nativeNode start.1 = EthLib.Cryptography.Sphincs.forsLeafHash EthLib.Cryptography.Sphincs.hashId
      (nativeNode seed) idx (trees j) (leaves j).val (nativeOpening (openings[j.val]!)).secret := by
    simpa only [EthLib.Cryptography.Sphincs.forsLeafHash,EthLib.Cryptography.Sphincs.adrsFors,
      hpositions j,opening_secret] using hs.1
  have hglobal := RustCrypto.ForsClimb.climb_global_eq
    ((pathNodes (openings[j.val]!) 10 0).map nativeNode) (nativeNode seed) idx (trees j) 0 (leaves j).val
    (nativeNode start.1) (by simp only [List.length_map,pathNodes_length]; omega)
  have hwalk : nativeNode (walk (openings[j.val]!) 10 0 (positions[j.val]!) start.1 start.2).1 =
      EthLib.Cryptography.Merkle.climb
        (EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx (trees j))
        ⟨0,(leaves j).val⟩ (nativeNode start.1) ((pathNodes (openings[j.val]!) 10 0).map nativeNode) := by
    rw [← hglobal]
    simpa only [hpositions j,EthLib.Cryptography.Sphincs.forsTreeIndex,
      EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT] using hw.1
  have hresult := hout j.val j.isLt
  have hnode := congrArg Prod.fst hresult
  have haddress := congrArg Prod.snd hresult
  dsimp only at hnode haddress
  constructor
  · rw [hnode,hwalk]
    simp only [EthLib.Cryptography.Sphincs.treeRecover,Bind.bind,hleaf,opening_path]
  · rw [haddress]
    exact hw.2

end RustCrypto.ForsBatch
