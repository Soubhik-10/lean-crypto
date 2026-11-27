module
public import RustCrypto.Wots.Recovery.Canonical
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

theorem little_bytes_roundtrip (values : List Byte) : (BitVec.fromLEBytes values).toLEBytes = values := by
  apply List.ext_getElem
  · simp only [BitVec.toLEBytes_length]
    omega
  · intro i hi hother
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change ((BitVec.fromLEBytes values).toLEBytes[i]).testBit j = (values[i]).testBit j
    rw [← getElem!_pos _ i hi,← getElem!_pos _ i hother]
    rw [BitVec.toLEBytes_getElem!_testBit _ i j hj,BitVec.fromLEBytes_getElem!]
    have hd : (8*i+j)/8 = i := by omega
    have hm : (8*i+j)%8 = j := by omega
    rw [hd,hm]

theorem little_bytes_cast (value : BitVec n) (h : n = m) : (value.cast h).toLEBytes = value.toLEBytes := by
  cases h
  rfl

theorem big_bytes_cast (value : BitVec n) (h : n = m) : (value.cast h).toBEBytes = value.toBEBytes := by
  cases h
  rfl

theorem big_bytes_roundtrip (values : List Byte) : (BitVec.fromBEBytes values).toBEBytes = values := by
  simp only [BitVec.fromBEBytes,BitVec.toBEBytes,little_bytes_cast,little_bytes_roundtrip,List.reverse_reverse]

/-- Every four-byte counter is preserved by the source big-endian decoder/encoder. -/
theorem counter_bytes_roundtrip (input : Aeneas.Std.Array U8 4#usize) :
    core.num.U32.to_be_bytes (core.num.U32.from_be_bytes input) = input := by
  apply Aeneas.Std.Array.ext
  simp only [core.num.U32.to_be_bytes,core.num.U32.from_be_bytes,Aeneas.Std.Array.from_val,U32.bv,
    big_bytes_cast,big_bytes_roundtrip,List.map_map,Function.comp_def,List.map_id']

end RustCrypto.WotsRecover
