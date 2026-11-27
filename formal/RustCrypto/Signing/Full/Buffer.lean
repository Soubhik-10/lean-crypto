module
public import RustCrypto.Signing.Full.Model
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

theorem native_bytes_length (bytes : List U8) : (nativeBytes bytes).length = bytes.length := by simp only [nativeBytes,List.length_map]

theorem native_bytes_set (bytes payload : List U8) (offset : Nat) :
    nativeBytes (bytes.setSlice! offset payload) = (nativeBytes bytes).setSlice! offset (nativeBytes payload) := by
  exact List.map_setSlice! bytes offset payload _

theorem overwrite_prefix {α : Type} (bytes payload : List α) (offset : Nat) (hroom : offset+payload.length ≤ bytes.length) :
    (bytes.setSlice! offset payload).take (offset+payload.length) = bytes.take offset ++ payload := by
  rw [WotsEthlib.overwrite_layout_any bytes payload offset hroom]
  simp (disch := omega) [List.take_append]

theorem overwrite_pair {α : Type} (bytes first second : List α) (hsize : bytes.length = first.length+second.length) :
    (bytes.setSlice! 0 first).setSlice! first.length second = first ++ second := by
  rw [WotsEthlib.overwrite_layout_any bytes first 0 (by omega)]
  simp only [List.take_zero,List.nil_append,Nat.zero_add]
  rw [WotsEthlib.overwrite_layout_any (first ++ bytes.drop first.length) second first.length (by simp only [List.length_append,List.length_drop]; omega)]
  simp only [List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil,List.drop_append,List.drop_eq_nil_iff.mpr (show first.length ≤ first.length+second.length by omega),
    List.nil_append,Nat.add_sub_cancel_left,List.drop_drop]
  have hd : bytes.drop (first.length+second.length) = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp only [hd,List.append_nil]

end RustCrypto.FullSign
