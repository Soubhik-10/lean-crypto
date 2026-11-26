module
public import RustCrypto.LayoutCounter
public import RustCrypto.LayoutDigests
public import RustCrypto.LayerInput
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem layer_room (bytes : List U8) (offset : Nat) (layer : EthLib.Cryptography.Sphincs.Layer)
    (hroom : offset+EthLib.Cryptography.Sphincs.Constants.layerSigSize layer.height ≤ bytes.length) :
    offset+1028+16*layer.height ≤ bytes.length := by
  simp only [EthLib.Cryptography.Sphincs.Constants.layerSigSize,EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN,
    EthLib.Cryptography.Sphincs.Constants.V,EthLib.Cryptography.Sphincs.Constants.N] at hroom
  omega

/-- Counter, all 64 chain values and every path node are exactly the reference layer decoder. -/
theorem layer_signature_decode (bytes : List U8) (offset : Nat) (layer : EthLib.Cryptography.Sphincs.Layer)
    (hroom : offset+EthLib.Cryptography.Sphincs.Constants.layerSigSize layer.height ≤ bytes.length) :
    LayerInput.signature (bytes.drop offset) layer = EthLib.Cryptography.Sphincs.decodeLayerSignature layer
      (RustCrypto.bytes bytes) offset (by simpa only [ByteBridge.bytes_size] using hroom) := by
  have hr := layer_room bytes offset layer hroom
  have hc := native_counter_read (bytes.drop offset) (by simp only [List.length_drop]; omega)
  have hs := read_bytes_shift bytes offset 0 EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN
    (by change offset+0+4 ≤ bytes.length; omega)
  simp only [Nat.add_zero] at hs
  have hv : WotsRecover.nativeValues ((bytes.drop offset).drop 4) =
      EthLib.Cryptography.Sphincs.splitDigests (EthLib.Base.readBytes (RustCrypto.bytes bytes)
        (offset+4) (EthLib.Cryptography.Sphincs.Constants.V*EthLib.Cryptography.Sphincs.Constants.N)
        (by rw [ByteBridge.bytes_size]; change offset+4+64*16 ≤ bytes.length; omega)) := by
    rw [native_values_path,List.drop_drop]
    have hd := ForsRead.nativePath_drop bytes EthLib.Cryptography.Sphincs.Constants.V (offset+4) 0
      (by change offset+4+0+16*64 ≤ bytes.length; omega)
    simp only [Nat.add_zero] at hd
    exact hd.trans (native_path_read bytes EthLib.Cryptography.Sphincs.Constants.V (offset+4)
      (by change offset+4+16*64 ≤ bytes.length; omega))
  have hp : ForsRead.nativePath (bytes.drop offset) layer.height 1028 =
      EthLib.Cryptography.Sphincs.splitDigests (EthLib.Base.readBytes (RustCrypto.bytes bytes)
        (offset+1028) (layer.height*EthLib.Cryptography.Sphincs.Constants.N)
        (by rw [ByteBridge.bytes_size]; change offset+1028+layer.height*16 ≤ bytes.length; omega)) := by
    rw [ForsRead.nativePath_drop bytes layer.height offset 1028 (by omega),
      native_path_read bytes layer.height (offset+1028) (by omega)]
  unfold LayerInput.signature EthLib.Cryptography.Sphincs.decodeLayerSignature
  rw [hc,hs,hv]
  change EthLib.Cryptography.Sphincs.LayerSignature.mk _ _ _ = EthLib.Cryptography.Sphincs.LayerSignature.mk _ _ _
  rw [hp]
  simp only [EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN,EthLib.Cryptography.Sphincs.Constants.V,EthLib.Cryptography.Sphincs.Constants.N,Nat.add_assoc]

end RustCrypto.Layout
