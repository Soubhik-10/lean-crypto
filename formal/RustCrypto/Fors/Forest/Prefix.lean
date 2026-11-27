module
public import RustCrypto.Fors.Forest.Model
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def nativeBytes (values : List U8) : List UInt8 := values.map (fun b => UInt8.ofBitVec b.bv)

theorem native_group {N : Usize} {n : Nat} (nodes : Aeneas.Std.Array Node N)
    (rows : Vector EthLib.Cryptography.Sphincs.Digest n) (start : Nat) (hstart : start+N.val ≤ n)
    (hrows : ∀ j (hj : j < N.val), nativeNode (nodes[j]!) = rows[start+j]'(by omega)) :
    nativeBytes (nodes.val.flatMap (fun node => node.val)) =
      ((rows.toList.drop start).take N.val).flatMap Vector.toList := by
  have hm : nodes.val.map nativeNode = (rows.toList.drop start).take N.val := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_take,List.length_drop,Vector.length_toList]
      have hl : nodes.val.length = N.val := nodes.property
      omega
    · intro j hj hother
      have hjn : j < N.val := by simpa only [List.length_map,← nodes.property] using hj
      rw [List.getElem_map,List.getElem_take,List.getElem_drop,Vector.getElem_toList]
      have h := hrows j hjn
      rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos nodes.val j (by simpa only [nodes.property] using hjn)] at h
      exact h
  have hf := congrArg (List.flatMap Vector.toList) hm
  simpa only [nativeBytes,List.map_flatMap,List.flatMap_map,native_node_list] using hf

theorem roots_before_add (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node)
    (idx start count : Nat) :
    rootsBefore bytes digest seed idx (start+count) = rootsBefore bytes digest seed idx start ++
      (((recoveredRoots bytes digest seed idx).toList.drop start).take count).flatMap Vector.toList := by
  unfold rootsBefore OrderedPrefix.collect
  rw [List.take_add,List.flatMap_append]

end RustCrypto.ForsForest
