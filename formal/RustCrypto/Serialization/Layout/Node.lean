module
public import RustCrypto.Serialization.Layout.Read
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem node_at_get (bytes : List U8) (offset i : Nat) (hi : i < 16) :
    (nativeNode (ForsRead.nodeAt bytes offset))[i]'hi = UInt8.ofBitVec (bytes[offset+i]!).bv := by
  simp only [nativeNode,Vector.getElem_mk,List.getElem_toArray,List.getElem_map,
    ForsRead.nodeAt,Aeneas.Std.Array.from_val,List.getElem_ofFn]

theorem node_list_get (bytes : List U8) (count offset i : Nat) (hi : i < count) :
    (ForsRead.nodeList bytes count offset)[i]'(by simpa only [ForsRead.nodeList_length] using hi) =
      ForsRead.nodeAt bytes (offset+16*i) := by
  induction count generalizing offset i with
  | zero => omega
  | succ count ih =>
    cases i with
    | zero => simp only [ForsRead.nodeList,List.getElem_cons_zero,Nat.mul_zero,Nat.add_zero]
    | succ i =>
      simp only [ForsRead.nodeList,List.getElem_cons_succ,ih (offset+16) i (by omega)]
      congr 1
      omega

theorem native_path_get (bytes : List U8) (count offset i : Nat) (hi : i < count) :
    (ForsRead.nativePath bytes count offset)[i]'hi = nativeNode (ForsRead.nodeAt bytes (offset+16*i)) := by
  simp only [ForsRead.nativePath,Vector.getElem_mk,List.getElem_toArray,List.getElem_map,node_list_get bytes count offset i hi]

end RustCrypto.Layout
