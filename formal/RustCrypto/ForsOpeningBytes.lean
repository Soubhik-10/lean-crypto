module
public import RustCrypto.ForsBatchBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def nativeOpeningBytes (opening : Aeneas.Std.Array U8 176#usize) :
    Vector UInt8 EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE :=
  ⟨(opening.val.map (fun b => UInt8.ofBitVec b.bv)).toArray,by simp [EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE,EthLib.Cryptography.Sphincs.Constants.N,EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT]⟩

def nativeOpening (opening : Aeneas.Std.Array U8 176#usize) : EthLib.Cryptography.Sphincs.TreeOpening :=
  EthLib.Cryptography.Sphincs.treeOpeningOfBytes (nativeOpeningBytes opening)

theorem nativeOpeningBytes_get (opening : Aeneas.Std.Array U8 176#usize) (i : Nat) (hi : i < 176) :
    (nativeOpeningBytes opening)[i]'hi = UInt8.ofBitVec (opening.val[i]!).bv := by
  have hindex : i < opening.val.length := by scalar_tac
  simp only [nativeOpeningBytes,Vector.getElem_mk,List.getElem_toArray,List.getElem_map,
    getElem!_pos opening.val i hindex]

theorem readNode_get (opening : Aeneas.Std.Array U8 176#usize) (level : Nat) (hlevel : level < 11)
    (i : Nat) (hi : i < 16) :
    (nativeNode (readNode opening level))[i]'hi = UInt8.ofBitVec (opening.val[16*level+i]!).bv := by
  rw [readNode_eq _ _ hlevel]
  simp only [nativeNode,Vector.getElem_mk,List.getElem_toArray,List.getElem_map,nodeAt_val,openingNode,
    List.getElem_take,List.getElem_drop]
  rw [getElem!_pos opening.val (16*level+i) (by scalar_tac)]

theorem pathNodes_get (opening : Aeneas.Std.Array U8 176#usize) (fuel level i : Nat) (hi : i < fuel) :
    (pathNodes opening fuel level)[i]'(by simpa only [pathNodes_length] using hi) = readNode opening (level+1+i) := by
  induction fuel generalizing level i with
  | zero => omega
  | succ fuel ih =>
    cases i with
    | zero => simp only [pathNodes,List.getElem_cons_zero,Nat.add_zero]
    | succ i =>
      simp only [pathNodes,List.getElem_cons_succ,ih (level+1) i (by omega)]
      congr 1
      omega

theorem opening_secret (opening : Aeneas.Std.Array U8 176#usize) :
    nativeNode (readNode opening 0) = (nativeOpening opening).secret := by
  apply Vector.ext
  intro i hi
  simp only [nativeNode,readNode_eq _ _ (by decide : 0 < 11),nodeAt_val,openingNode,
    nativeOpening,EthLib.Cryptography.Sphincs.treeOpeningOfBytes,nativeOpeningBytes,
    Vector.getElem_ofFn,Vector.getElem_mk,List.getElem_toArray,List.getElem_map,
    List.getElem_take,List.getElem_drop,Nat.mul_zero,Nat.zero_add]

theorem opening_path (opening : Aeneas.Std.Array U8 176#usize) :
    (pathNodes opening 10 0).map nativeNode = (nativeOpening opening).path.toList := by
  apply List.ext_getElem
  · simp only [List.length_map,pathNodes_length]
    have hlen : (nativeOpening opening).path.toList.length = 10 := Vector.length_toList
    exact hlen.symm
  · intro i hi hother
    have hi10 : i < 10 := by simpa only [List.length_map,pathNodes_length] using hi
    rw [List.getElem_map,pathNodes_get opening 10 0 i hi10]
    simp only [Nat.zero_add]
    rw [Vector.getElem_toList]
    apply Vector.ext
    intro j hj
    have hj16 : j < 16 := hj
    rw [readNode_get opening (1+i) (by omega) j hj]
    simp only [nativeOpening,EthLib.Cryptography.Sphincs.treeOpeningOfBytes,
      EthLib.Cryptography.Sphincs.splitDigests,EthLib.Cryptography.Sphincs.splitChunks,Vector.getElem_ofFn]
    have hbyte := nativeOpeningBytes_get opening
      (EthLib.Cryptography.Sphincs.Constants.N + (i*EthLib.Cryptography.Sphincs.Constants.N+j)) (by
        change 16+(i*16+j) < 176
        omega)
    have hindex : EthLib.Cryptography.Sphincs.Constants.N + (i*EthLib.Cryptography.Sphincs.Constants.N+j) = 16*(1+i)+j := by
      change 16+(i*16+j) = 16*(1+i)+j
      omega
    calc
      _ = UInt8.ofBitVec (opening.val[EthLib.Cryptography.Sphincs.Constants.N + (i*EthLib.Cryptography.Sphincs.Constants.N+j)]!).bv := by
        rw [hindex]
      _ = _ := hbyte.symm

end RustCrypto.ForsBatch
