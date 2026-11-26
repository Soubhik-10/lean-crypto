module
public import RustCrypto.LayoutDigests
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem opening_ext (a b : EthLib.Cryptography.Sphincs.TreeOpening) (hs : a.secret = b.secret) (hp : a.path = b.path) : a = b := by
  cases a
  cases b
  cases hs
  cases hp
  rfl

/-- Reference decoding of one opening agrees with the scalar source byte model. -/
theorem opening_read (bytes : List U8) (offset : Nat) (hroom : offset+176 ≤ bytes.length) :
    EthLib.Cryptography.Sphincs.treeOpeningOfBytes
      (EthLib.Base.readBytes (RustCrypto.bytes bytes) offset EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE
        (by rw [ByteBridge.bytes_size]; exact hroom)) = ForsRead.decodedOpening bytes offset := by
  apply opening_ext
  · apply Vector.ext
    intro j hj
    simp only [EthLib.Cryptography.Sphincs.treeOpeningOfBytes,Vector.getElem_ofFn,ForsRead.decodedOpening]
    have hr := read_bytes_get bytes offset EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE hroom j
      (by change j < 176; have hj16 : j < 16 := hj; omega)
    calc
      _ = UInt8.ofBitVec (bytes[offset+j]!).bv := hr
      _ = _ := (node_at_get bytes offset j hj).symm
  · have hp : (Vector.ofFn (fun j : Fin (EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT*EthLib.Cryptography.Sphincs.Constants.N) =>
        (EthLib.Base.readBytes (RustCrypto.bytes bytes) offset EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE
          (by rw [ByteBridge.bytes_size]; exact hroom))[EthLib.Cryptography.Sphincs.Constants.N+j.val]'(by have hj := j.isLt; change 16+j.val < 176; change j.val < 10*16 at hj; omega))) =
        EthLib.Base.readBytes (RustCrypto.bytes bytes) (offset+16)
          (EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT*EthLib.Cryptography.Sphincs.Constants.N)
          (by rw [ByteBridge.bytes_size]; change offset+16+10*16 ≤ bytes.length; omega) := by
      apply Vector.ext
      intro j hj
      simp only [Vector.getElem_ofFn]
      have ha := read_bytes_get bytes offset EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE hroom
        (EthLib.Cryptography.Sphincs.Constants.N+j) (by change 16+j < 176; change j < 10*16 at hj; omega)
      have hb := read_bytes_get bytes (offset+16)
        (EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT*EthLib.Cryptography.Sphincs.Constants.N)
        (by change offset+16+10*16 ≤ bytes.length; omega) j hj
      have he : offset+(EthLib.Cryptography.Sphincs.Constants.N+j) = offset+16+j := by
        change offset+(16+j) = offset+16+j
        omega
      calc
        _ = UInt8.ofBitVec (bytes[offset+(EthLib.Cryptography.Sphincs.Constants.N+j)]!).bv := ha
        _ = UInt8.ofBitVec (bytes[offset+16+j]!).bv := by rw [he]
        _ = _ := hb.symm
    simp only [EthLib.Cryptography.Sphincs.treeOpeningOfBytes,ForsRead.decodedOpening]
    rw [hp]
    exact (native_path_read bytes EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT (offset+16)
      (by change offset+16+16*10 ≤ bytes.length; omega)).symm

end RustCrypto.Layout
