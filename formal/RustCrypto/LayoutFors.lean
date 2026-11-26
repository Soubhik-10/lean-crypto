module
public import RustCrypto.LayoutOpening
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

/-- Every reference chunk is the same contiguous byte read at its computed offset. -/
theorem split_chunk_read (bytes : List U8) (offset count chunk : Nat)
    (hroom : offset+count*chunk ≤ bytes.length) (i : Nat) (hi : i < count) :
    (EthLib.Cryptography.Sphincs.splitChunks (EthLib.Base.readBytes (RustCrypto.bytes bytes) offset (count*chunk)
      (by rw [ByteBridge.bytes_size]; exact hroom)))[i]'hi =
      EthLib.Base.readBytes (RustCrypto.bytes bytes) (offset+i*chunk) chunk
        (by rw [ByteBridge.bytes_size]; have hm := Nat.mul_le_mul_right chunk (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at hm; omega) := by
  apply Vector.ext
  intro j hj
  simp only [EthLib.Cryptography.Sphincs.splitChunks,Vector.getElem_ofFn]
  have hm := Nat.mul_le_mul_right chunk (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  have ha := read_bytes_get bytes offset (count*chunk) hroom (i*chunk+j) (by omega)
  have hb := read_bytes_get bytes (offset+i*chunk) chunk (by omega) j hj
  calc
    _ = UInt8.ofBitVec (bytes[offset+(i*chunk+j)]!).bv := ha
    _ = UInt8.ofBitVec (bytes[offset+i*chunk+j]!).bv := by rw [Nat.add_assoc]
    _ = _ := hb.symm

theorem opening_shift (bytes : List U8) (offset inner : Nat) (hroom : offset+inner+176 ≤ bytes.length) :
    ForsRead.decodedOpening (bytes.drop offset) inner = ForsRead.decodedOpening bytes (offset+inner) := by
  unfold ForsRead.decodedOpening
  rw [ForsRead.nodeAt_drop bytes offset inner (by omega),
    ForsRead.nativePath_drop bytes 10 offset (inner+16) (by omega)]
  simp only [Nat.add_assoc]

/-- All 24 decoded FORS openings have the scalar source model's exact bytes. -/
theorem fors_decode (bytes : List U8) (offset : Nat) (hroom : offset+4224 ≤ bytes.length) :
    EthLib.Cryptography.Sphincs.decodeFors (RustCrypto.bytes bytes) offset
      (by rw [ByteBridge.bytes_size]; exact hroom) = ForsRead.decodedOpenings (bytes.drop offset) := by
  apply Vector.ext
  intro i hi
  simp only [EthLib.Cryptography.Sphincs.decodeFors,Vector.getElem_map,ForsRead.decodedOpenings,Vector.getElem_ofFn]
  have hi24 : i < 24 := hi
  rw [split_chunk_read bytes offset EthLib.Cryptography.Sphincs.Constants.FORS_TREES
    EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE hroom i hi]
  have ho := opening_read bytes (offset+i*EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE)
    (by change offset+i*176+176 ≤ bytes.length; omega)
  rw [ho]
  have hs := opening_shift bytes offset (176*i) (by omega)
  have he : offset+i*EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE = offset+176*i := by
    change offset+i*176 = offset+176*i
    omega
  rw [he]
  exact hs.symm

end RustCrypto.Layout
