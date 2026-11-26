module
public import RustCrypto.ForsScalarBytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsRead
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def nativeBytes (values : List U8) : List UInt8 := values.map (fun b => UInt8.ofBitVec b.bv)

theorem nodeAt_drop (bytes : List U8) (offset inner : Nat) (hroom : offset+inner+16 ≤ bytes.length) :
    nodeAt (bytes.drop offset) inner = nodeAt bytes (offset+inner) := by
  apply Aeneas.Std.Array.ext
  rw [nodeAt_val _ inner (by simp only [List.length_drop]; omega),nodeAt_val _ (offset+inner) hroom,List.drop_drop]

theorem nodeList_drop (bytes : List U8) (count offset inner : Nat) (hroom : offset+inner+16*count ≤ bytes.length) :
    nodeList (bytes.drop offset) count inner = nodeList bytes count (offset+inner) := by
  induction count generalizing inner with
  | zero => rfl
  | succ count ih =>
    simp only [nodeList]
    rw [nodeAt_drop bytes offset inner (by omega),ih (inner+16) (by omega)]
    rw [Nat.add_assoc]

theorem nativePath_drop (bytes : List U8) (count offset inner : Nat) (hroom : offset+inner+16*count ≤ bytes.length) :
    nativePath (bytes.drop offset) count inner = nativePath bytes count (offset+inner) := by
  apply Vector.toList_inj.1
  rw [nativePath_list,nativePath_list,nodeList_drop bytes count offset inner hroom]

theorem decodedOpening_drop (bytes : List U8) (offset : Nat) (hroom : offset+176 ≤ bytes.length) :
    decodedOpening (bytes.drop offset) 0 = decodedOpening bytes offset := by
  unfold decodedOpening
  rw [nodeAt_drop bytes offset 0 (by omega),nativePath_drop bytes 10 offset (0+16) (by omega)]
  simp only [Nat.add_zero,Nat.zero_add]

theorem roots_before_succ (bytes : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node)
    (idx count : Nat) (hcount : count < 24) :
    rootsBefore bytes digest seed idx (count+1) = rootsBefore bytes digest seed idx count ++
      (recovered bytes digest seed idx ⟨count,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hcount⟩).toList := by
  unfold rootsBefore
  rw [OrderedPrefix.prefix_succ (recoveredRoots bytes digest seed idx) Vector.toList count
    (by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hcount)]
  simp only [recoveredRoots,Vector.getElem_ofFn]

end RustCrypto.ForsRead
