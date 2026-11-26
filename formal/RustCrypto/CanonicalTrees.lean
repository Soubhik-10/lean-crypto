module
public import RustCrypto.CanonicalMerkle
public import RustCrypto.OrderedVector
public import EthLib.Cryptography.Sphincs.Fors
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
open EthLib.Cryptography
open EthLib.Cryptography.Sphincs
variable (hash : ByteArray → Id (Vector UInt8 32))

theorem built_path {α : Type} (parent : Merkle.Position → α → α → Id α) (leaves : Nat → Id α)
    (height index : Nat) (hb : index < 2^height) :
    (Merkle.build parent leaves ⟨height,0⟩).path height index = Merkle.path parent leaves height index := by
  apply Vector.toList_inj.1
  rw [RustCrypto.MerklePath.build_path_list parent leaves height 0 index (Nat.div_eq_of_lt hb)]
  unfold Merkle.path
  rw [RustCrypto.MerklePath.siblings_list]
  simp only [Nat.zero_add]

theorem xmss_fold_path (seed : PkSeed) (prf : Prf Id) (layer : Layer) (tree index : Nat)
    (hb : index < 2^layer.height) :
    fold hash seed layer tree index (leaves hash seed prf layer tree index) (path hash seed prf layer tree index) =
      treeRoot hash seed prf layer tree :=
  climb_path (nodeHash hash seed layer tree) (leaves hash seed prf layer tree) layer.height index hb

theorem tree_recover_open (seed : PkSeed) (prf : Prf Id) (index : Nat) (tree : Fin Constants.FORS_TREES)
    (leaf : Fin (2^Constants.FORS_HEIGHT)) :
    treeRecover hash seed index tree leaf (treeOpen hash seed prf index tree leaf).1 =
      (treeOpen hash seed prf index tree leaf).2 := by
  change Merkle.climb (forsNodeHash hash seed index tree) ⟨0,leaf.val⟩
      (forsLeaves hash seed prf index tree leaf.val)
      ((Merkle.build (forsNodeHash hash seed index tree) (forsLeaves hash seed prf index tree)
        ⟨Constants.FORS_HEIGHT,0⟩).path Constants.FORS_HEIGHT leaf.val).toList =
    (Merkle.build (forsNodeHash hash seed index tree) (forsLeaves hash seed prf index tree)
      ⟨Constants.FORS_HEIGHT,0⟩).value
  rw [built_path _ _ Constants.FORS_HEIGHT leaf.val leaf.isLt]
  calc
    _ = Merkle.root (forsNodeHash hash seed index tree) (forsLeaves hash seed prf index tree) Constants.FORS_HEIGHT :=
      climb_path _ _ _ _ leaf.isLt
    _ = _ := (RustCrypto.MerklePath.build_value _ _ Constants.FORS_HEIGHT 0).symm

theorem recover_openings (seed : PkSeed) (index : Nat)
    (choices : Vector (Fin (2^Constants.FORS_HEIGHT)) Constants.FORS_TREES)
    (opened : Vector (TreeOpening × Digest) Constants.FORS_TREES)
    (hopen : ∀ tree : Fin Constants.FORS_TREES,
      treeRecover hash seed index tree choices[tree] opened[tree].1 = opened[tree].2) :
    forsRecover hash seed index choices (opened.map Prod.fst) =
      forsPkFromRoots hash seed index (opened.map Prod.snd) := by
  unfold forsRecover
  simp only [RustCrypto.OrderedVector.ofFnInOrder_id,Bind.bind]
  apply congrArg (forsPkFromRoots hash seed index)
  apply Vector.ext
  intro tree ht
  simpa only [Fin.getElem_fin,Vector.getElem_ofFn,Vector.getElem_map] using hopen ⟨tree,ht⟩

theorem fors_recover_sign (seed : PkSeed) (prf : Prf Id) (index : Nat)
    (choices : Vector (Fin (2^Constants.FORS_HEIGHT)) Constants.FORS_TREES) :
    forsRecover hash seed index choices (forsSign hash seed prf index choices).1 =
      (forsSign hash seed prf index choices).2 := by
  let opened := Vector.ofFn (fun tree : Fin Constants.FORS_TREES =>
    treeOpen hash seed prf index tree choices[tree])
  have hs : forsSign hash seed prf index choices =
      (opened.map Prod.fst,forsPkFromRoots hash seed index (opened.map Prod.snd)) := by
    unfold forsSign
    simp only [RustCrypto.OrderedVector.ofFnInOrder_id,Bind.bind,Pure.pure]
    rfl
  rw [hs]
  apply recover_openings hash seed index choices opened
  rintro ⟨tree,ht⟩
  simpa only [opened,Fin.getElem_fin,Vector.getElem_ofFn] using
    tree_recover_open hash seed prf index ⟨tree,ht⟩ choices[tree]

end RustCrypto.CanonicalCorrectness
