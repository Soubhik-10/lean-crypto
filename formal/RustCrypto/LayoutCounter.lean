module
public import RustCrypto.LayoutRead
public import RustCrypto.WotsCounterBytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Layout
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem decode_four_bits (a b c d : BitVec 8) : BitVec.fromLEBytes [d,c,b,a] = (a ++ b ++ c ++ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by simpa using hi
  interval_cases i <;> simp only [BitVec.getLsbD_append] <;> simp [BitVec.fromLEBytes]

theorem field32_val (a b c d : U8) :
    (core.num.U32.from_be_bytes (Aeneas.Std.Array.make 4#usize [a,b,c,d])).val =
      16777216*a.val+65536*b.val+256*c.val+d.val := by
  change (BitVec.fromLEBytes [d.bv,c.bv,b.bv,a.bv]).toNat = _
  rw [decode_four_bits]
  simp only [BitVec.toNat_append_eq_mul_add]
  change ((a.val*256+b.val)*256+c.val)*256+d.val = _
  omega

theorem array_four (input : Aeneas.Std.Array U8 4#usize) : input.val =
    [input.val[0]!,input.val[1]!,input.val[2]!,input.val[3]!] := by
  have hl : input.val.length = 4 := input.property
  apply List.ext_getElem
  · simp only [hl]
    rfl
  · intro i hi hother
    have hi4 : i < 4 := by simpa only [hl] using hi
    interval_cases i <;> simp (disch := omega) [getElem!_pos]

theorem native_word_from_be (input : Aeneas.Std.Array U8 4#usize) :
    (UInt32.ofBitVec (core.num.U32.from_be_bytes input).bv).toNat =
      EthLib.Base.ByteOrder.ofBE (input.val.map (fun b => UInt8.ofBitVec b.bv)) := by
  have he : input = Aeneas.Std.Array.make 4#usize [input.val[0]!,input.val[1]!,input.val[2]!,input.val[3]!] := by
    apply Aeneas.Std.Array.ext
    rw [Aeneas.Std.Array.make_val]
    exact array_four input
  have hw : (core.num.U32.from_be_bytes input).val =
      16777216*(input.val[0]!).val+65536*(input.val[1]!).val+256*(input.val[2]!).val+(input.val[3]!).val := by
    exact (congrArg (fun a : Aeneas.Std.Array U8 4#usize => (core.num.U32.from_be_bytes a).val) he).trans
      (field32_val _ _ _ _)
  rw [UInt32.toNat_ofBitVec,U32.bv_toNat,hw,array_four input]
  simp only [List.map_cons,List.map_nil,EthLib.Base.ByteOrder.ofBE_eq_foldl,List.foldl_cons,List.foldl_nil,
    UInt8.toNat_ofBitVec,U8.bv_toNat]
  simp
  omega

theorem native_counter_value (bytes : List U8) (hroom : 4 ≤ bytes.length) :
    (WotsRecover.nativeCounter bytes).toNat =
      EthLib.Cryptography.Sphincs.toInt (EthLib.Base.readBytes (RustCrypto.bytes bytes) 0
        EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN (by simpa only [ByteBridge.bytes_size,EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN] using hroom)) := by
  unfold WotsRecover.nativeCounter EthLib.Cryptography.Sphincs.toInt
  rw [native_word_from_be,WotsRecover.counterBytes_val bytes hroom]
  have hr := read_bytes_list bytes 0 EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN (by exact hroom)
  simp only [List.drop_zero] at hr
  rw [hr]
  rfl

theorem native_counter_read (bytes : List U8) (hroom : 4 ≤ bytes.length) :
    WotsRecover.nativeCounter bytes = UInt32.ofNat
      (EthLib.Cryptography.Sphincs.toInt (EthLib.Base.readBytes (RustCrypto.bytes bytes) 0
        EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN (by simpa only [ByteBridge.bytes_size,EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN] using hroom))) := by
  rw [←native_counter_value bytes hroom]
  exact Eq.symm UInt32.ofNat_toNat

end RustCrypto.Layout
