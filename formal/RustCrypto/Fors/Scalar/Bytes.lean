module
public import RustCrypto.Fors.Climb
public import RustCrypto.Fors.DigestBridge
public import RustCrypto.Common.OrderedPrefix
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsRead
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def nodeAt (bytes : List U8) (offset : Nat) : Node :=
  Aeneas.Std.Array.from (List.ofFn (fun i : Fin 16 => bytes[offset+i.val]!)) (by simp)

theorem nodeAt_val (bytes : List U8) (offset : Nat) (hroom : offset+16 ≤ bytes.length) :
    (nodeAt bytes offset).val = (bytes.drop offset).take 16 := by
  apply List.ext_getElem
  · simp only [nodeAt,Aeneas.Std.Array.from_val,List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hother
    simp only [nodeAt,Aeneas.Std.Array.from_val,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
    rw [getElem!_pos bytes (offset+i) (by simp only [nodeAt,Aeneas.Std.Array.from_val,List.length_ofFn] at hi; omega)]

def nodeList (bytes : List U8) : Nat → Nat → List Node
  | 0,_ => []
  | count+1,offset => nodeAt bytes offset :: nodeList bytes count (offset+16)

@[simp] theorem nodeList_length (bytes : List U8) (count offset : Nat) :
    (nodeList bytes count offset).length = count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih => simp only [nodeList,List.length_cons,ih]

theorem serialized_nodes (bytes : List U8) (count offset : Nat) (hroom : offset+16*count ≤ bytes.length) :
    nodesBytes (nodeList bytes count offset) = (bytes.drop offset).take (16*count) := by
  induction count generalizing offset with
  | zero => simp only [nodeList,nodesBytes,List.flatMap_nil,Nat.mul_zero,List.take_zero]
  | succ count ih =>
    simp only [nodeList,nodesBytes,List.flatMap_cons]
    have ht := ih (offset+16) (by omega)
    simp only [nodesBytes] at ht
    rw [nodeAt_val bytes offset (by omega),ht]
    have hc : 16*(count+1) = 16+16*count := by omega
    rw [hc,List.take_add,List.drop_drop]

def nativePath (bytes : List U8) (count offset : Nat) : Vector EthLib.Cryptography.Sphincs.Digest count :=
  ⟨((nodeList bytes count offset).map nativeNode).toArray,by simp⟩

@[simp] theorem nativePath_list (bytes : List U8) (count offset : Nat) :
    (nativePath bytes count offset).toList = (nodeList bytes count offset).map nativeNode := by
  simp only [nativePath,Vector.toList_mk]

def decodedOpening (bytes : List U8) (offset : Nat) : EthLib.Cryptography.Sphincs.TreeOpening :=
  ⟨nativeNode (nodeAt bytes offset),nativePath bytes 10 (offset+16)⟩

def decodedOpenings (bytes : List U8) :
    Vector EthLib.Cryptography.Sphincs.TreeOpening EthLib.Cryptography.Sphincs.Constants.FORS_TREES :=
  Vector.ofFn (fun tree => decodedOpening bytes (176*tree.val))

@[irreducible] def recovered (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) : EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.treeRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx tree
    ((EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[tree])
    (decodedOpening bytes (176*tree.val))

def recoveredRoots (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) :
    Vector EthLib.Cryptography.Sphincs.Digest EthLib.Cryptography.Sphincs.Constants.FORS_TREES :=
  Vector.ofFn (recovered bytes digest seed idx)

def rootsBefore (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx count : Nat) : List UInt8 :=
  OrderedPrefix.collect (recoveredRoots bytes digest seed idx) (fun root => root.toList) count

end RustCrypto.ForsRead
