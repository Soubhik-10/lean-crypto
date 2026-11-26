module
public import RustCrypto.ForsForestRead
public import RustCrypto.OrderedPrefix
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def openingAt (bytes : List U8) (offset : Nat) : Aeneas.Std.Array U8 176#usize :=
  Aeneas.Std.Array.from (List.ofFn (fun i : Fin 176 => bytes[offset+i.val]!)) (by simp)

theorem openingAt_val (bytes : List U8) (offset : Nat) (hroom : offset+176 ≤ bytes.length) :
    (openingAt bytes offset).val = (bytes.drop offset).take 176 := by
  apply List.ext_getElem
  · simp only [openingAt,Aeneas.Std.Array.from_val,List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hother
    simp only [openingAt,Aeneas.Std.Array.from_val,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
    rw [getElem!_pos bytes (offset+i) (by simp only [openingAt,Aeneas.Std.Array.from_val,List.length_ofFn] at hi; omega)]

theorem openingAt_drop (bytes : List U8) (offset inner : Nat) (hroom : offset+inner+176 ≤ bytes.length) :
    openingAt (bytes.drop offset) inner = openingAt bytes (offset+inner) := by
  apply Aeneas.Std.Array.ext
  rw [openingAt_val _ inner (by simp only [List.length_drop]; omega),openingAt_val _ (offset+inner) hroom,
    List.drop_drop]

@[irreducible] def recovered (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) : EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.treeRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx tree
    ((EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[tree])
    (ForsBatch.nativeOpening (openingAt bytes (176*tree.val)))

def recoveredRoots (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) :
    Vector EthLib.Cryptography.Sphincs.Digest EthLib.Cryptography.Sphincs.Constants.FORS_TREES :=
  Vector.ofFn (recovered bytes digest seed idx)

def rootsBefore (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx count : Nat) : List UInt8 :=
  OrderedPrefix.collect (recoveredRoots bytes digest seed idx) (fun root => root.toList) count

end RustCrypto.ForsForest
