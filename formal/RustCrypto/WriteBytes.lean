module
public import RustCrypto.ReadBytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ByteBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Source little-endian serialization agrees byte for byte with EthLib's word serializer. -/
theorem encode_eight (input : U64) :
    (core.num.U64.to_le_bytes input).val.map (fun value => UInt8.ofBitVec value.bv) =
      EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane (word input) := by
  simp only [core.num.U64.to_le_bytes, Aeneas.Std.Array.from_val, List.map_map]
  change input.bv.toLEBytes.map UInt8.ofBitVec = _
  apply List.ext_getElem
  · simp [BitVec.toLEBytes_length, EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane]
  · intro i hi hother
    have hi8 : i < 8 := by simpa [BitVec.toLEBytes_length] using hi
    interval_cases i <;>
      apply UInt8.toBitVec_inj.1 <;>
      simp [BitVec.toLEBytes, EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane, word]
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      interval_cases j <;> simp

end RustCrypto.ByteBridge
