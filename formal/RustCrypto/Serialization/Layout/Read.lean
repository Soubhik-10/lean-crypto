module
public import RustCrypto.Fors.Scalar.Layout
public import RustCrypto.Wots.Encoding.Read
public import RustCrypto.Verification.Message.Full
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem read_bytes_list (bytes : List U8) (offset count : Nat) (hroom : offset+count ≤ bytes.length) :
    (EthLib.Base.readBytes (RustCrypto.bytes bytes) offset count (by simpa only [ByteBridge.bytes_size] using hroom)).toList =
      ((bytes.drop offset).take count).map (fun b => UInt8.ofBitVec b.bv) := by
  apply List.ext_getElem
  · simp only [Vector.length_toList,List.length_map,List.length_take,List.length_drop]
    omega
  · intro i hi hother
    rw [Vector.getElem_toList]
    simp only [EthLib.Base.readBytes,Vector.getElem_ofFn,List.getElem_map,List.getElem_take,List.getElem_drop]
    exact ByteBridge.bytes_get bytes (offset+i) (by simp only [Vector.length_toList] at hi; omega)

theorem node_read (bytes : List U8) (offset : Nat) (hroom : offset+16 ≤ bytes.length) :
    nativeNode (ForsRead.nodeAt bytes offset) =
      EthLib.Base.readBytes (RustCrypto.bytes bytes) offset EthLib.Cryptography.Sphincs.Constants.N
        (by simpa only [ByteBridge.bytes_size,EthLib.Cryptography.Sphincs.Constants.N] using hroom) := by
  apply Vector.toList_inj.1
  rw [native_node_list,ForsRead.nodeAt_val bytes offset hroom]
  exact (read_bytes_list bytes offset 16 hroom).symm

theorem read_bytes_get (bytes : List U8) (offset count : Nat) (hroom : offset+count ≤ bytes.length)
    (i : Nat) (hi : i < count) :
    (EthLib.Base.readBytes (RustCrypto.bytes bytes) offset count (by simpa only [ByteBridge.bytes_size] using hroom))[i]'hi =
      UInt8.ofBitVec (bytes[offset+i]!).bv := by
  simp only [EthLib.Base.readBytes,Vector.getElem_ofFn]
  rw [ByteBridge.bytes_get bytes (offset+i) (by omega),getElem!_pos bytes (offset+i) (by omega)]

end RustCrypto.Layout
