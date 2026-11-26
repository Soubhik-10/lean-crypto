module
public import RustCrypto.ForsForestModel
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def treeAt (start : Usize) (lane : Fin width) (hstart : start.val+width ≤ 24) :
    Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES :=
  ⟨start.val+lane.val,by
    change start.val+lane.val < 24
    have hl : lane.val < width := lane.isLt
    omega⟩

def leafAt (digest : Aeneas.Std.Array U8 34#usize) (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) :=
  (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[tree]

theorem leafAt_val (digest : Aeneas.Std.Array U8 34#usize)
    (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) :
    (leafAt digest tree).val = EthLib.Cryptography.Sphincs.msbField (RustCrypto.ForsDigest.nativeDigest digest)
      (10*tree.val) 10 := by
  simp only [leafAt,EthLib.Cryptography.Sphincs.digestLeaves,Fin.getElem_fin,Vector.getElem_ofFn]
  rfl

@[step] theorem forest_body_spec (reader : Slice U8) (roots : List U8)
    (addresses : Aeneas.Std.Array Address 2#usize) (digest : Aeneas.Std.Array U8 34#usize)
    (seed : Node) (idx : Nat) (start : Usize) (hstart : start.val+width ≤ 24)
    (hreader : 352 ≤ reader.val.length)
    (hframes : ∀ j : Fin width, keyFrame (addresses[j.val]!) seed
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop.body digest reader roots addresses start ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextReader,nextRoots,nextAddresses,nextStart) =>
          nextStart.val = start.val+width ∧ nextReader.val = reader.val.drop 352 ∧
          ∃ nodes : Aeneas.Std.Array Node 2#usize,
            nextRoots = roots ++ nodes.val.flatMap (fun node => node.val) ∧
            (∀ j : Fin width, nativeNode (nodes[j.val]!) =
              EthLib.Cryptography.Sphincs.treeRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx
                (treeAt start j hstart) (leafAt digest (treeAt start j hstart))
                (ForsBatch.nativeOpening (openingAt reader.val (176*j.val)))) ∧
            (∀ j : Fin width, keyFrame (nextAddresses[j.val]!) seed
              (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) ⦄ := by
  unfold lean_sphincs.fors.recover_trees_loop.body
  have hrange : start < lean_sphincs.params.FORS_TREES := by
    simp only [lean_sphincs.params.FORS_TREES]
    have hw : 0 < width := by decide
    scalar_tac
  simp only [ite_eq_left hrange]
  rw [RustParser.take_success 352#usize reader hreader]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  step as ⟨slice,hslice⟩
  rw [hslice]
  simp only [core.slice.Slice.as_chunks]
  have hn : ¬(176#usize).val = 0 := by decide
  simp only [ite_eq_right hn]
  step with first_batch_spec (RustParser.readPrefix 352#usize reader hreader) as ⟨openingOption,batch,hbatchOption,hbatch⟩
  rw [hbatchOption]
  step with position_array_spec digest start hstart as ⟨positions,hpositions⟩
  have hp : ∀ j : Fin width, (positions[j.val]!).val =
      EthLib.Cryptography.Sphincs.forsTreeIndex (treeAt start j hstart) 0 (leafAt digest (treeAt start j hstart)).val := by
    intro j
    simpa only [EthLib.Cryptography.Sphincs.forsTreeIndex,EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT,
      Nat.sub_zero,Nat.reducePow,leafAt_val,treeAt] using hpositions j.val j.isLt
  step with ForsBatch.recover_batch_ethlib_spec addresses batch positions seed idx
    (fun j => treeAt start j hstart) (fun j => leafAt digest (treeAt start j hstart)) hp hframes
    as ⟨nodes,nextAddresses,hrecovered⟩
  step with RustCrypto.AppendNodes.append_nodes_spec nodes roots as ⟨nextRoots,hnextRoots⟩
  step as ⟨nextStart,hnextStart⟩ by simp only [lean_sphincs.hash.batch.WIDTH]; scalar_tac
  refine ⟨?_,?_,nodes,hnextRoots,?_,?_⟩
  · have hw : (2#usize).val = width := rfl
    simpa only [lean_sphincs.hash.batch.WIDTH,hw] using hnextStart
  · have hsize : (352#usize).val = 352 := rfl
    simp only [RustParser.readSuffix,Slice.from_val,hsize]
  · intro j
    have hb : batch[j.val]! = openingAt reader.val (176*j.val) := by
      apply Aeneas.Std.Array.ext
      rw [hbatch j.val j.isLt,openingAt_val _ _ (by have hj := j.isLt; simp only [width] at hj; omega)]
      simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val]
      have hsize : (352#usize).val = 352 := rfl
      rw [hsize,List.drop_take,List.take_take,Nat.min_eq_left (by have hj := j.isLt; simp only [width] at hj; omega)]
    simpa only [hb] using (hrecovered j).1
  · intro j
    exact (hrecovered j).2

end RustCrypto.ForsForest
