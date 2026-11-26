module
public import RustCrypto.LayoutNode
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

theorem read_bytes_shift (bytes : List U8) (offset inner count : Nat) (hroom : offset+inner+count ≤ bytes.length) :
    EthLib.Base.readBytes (RustCrypto.bytes (bytes.drop offset)) inner count
      (by rw [ByteBridge.bytes_size,List.length_drop]; omega) =
    EthLib.Base.readBytes (RustCrypto.bytes bytes) (offset+inner) count (by rw [ByteBridge.bytes_size]; exact hroom) := by
  apply Vector.toList_inj.1
  rw [read_bytes_list (bytes.drop offset) inner count (by rw [List.length_drop]; omega),
    read_bytes_list bytes (offset+inner) count hroom,List.drop_drop]

theorem native_path_read (bytes : List U8) (count offset : Nat) (hroom : offset+16*count ≤ bytes.length) :
    ForsRead.nativePath bytes count offset = EthLib.Cryptography.Sphincs.splitDigests
      (EthLib.Base.readBytes (RustCrypto.bytes bytes) offset (count*EthLib.Cryptography.Sphincs.Constants.N)
        (by rw [ByteBridge.bytes_size]; change offset+count*16 ≤ bytes.length; omega)) := by
  apply Vector.ext
  intro i hi
  have hv := native_path_get bytes count offset i hi
  rw [hv]
  apply Vector.ext
  intro j hj
  simp only [EthLib.Cryptography.Sphincs.splitDigests,EthLib.Cryptography.Sphincs.splitChunks,Vector.getElem_ofFn]
  have hj16 : j < 16 := hj
  have hr := read_bytes_get bytes offset (count*EthLib.Cryptography.Sphincs.Constants.N)
    (by change offset+count*16 ≤ bytes.length; omega)
    (i*EthLib.Cryptography.Sphincs.Constants.N+j) (by change i*16+j < count*16; omega)
  have hn := node_at_get bytes (offset+16*i) j hj16
  have he : offset+16*i+j = offset+(i*EthLib.Cryptography.Sphincs.Constants.N+j) := by
    change offset+16*i+j = offset+(i*16+j)
    omega
  calc
    _ = UInt8.ofBitVec (bytes[offset+16*i+j]!).bv := hn
    _ = UInt8.ofBitVec (bytes[offset+(i*EthLib.Cryptography.Sphincs.Constants.N+j)]!).bv := by rw [he]
    _ = _ := hr.symm

theorem native_values_path (bytes : List U8) : WotsRecover.nativeValues bytes = ForsRead.nativePath bytes EthLib.Cryptography.Sphincs.Constants.V 0 := by
  apply Vector.ext
  intro i hi
  simp only [WotsRecover.nativeValues,Vector.getElem_ofFn]
  have hp := native_path_get bytes EthLib.Cryptography.Sphincs.Constants.V 0 i hi
  simpa only [Nat.zero_add] using hp.symm

end RustCrypto.Layout
