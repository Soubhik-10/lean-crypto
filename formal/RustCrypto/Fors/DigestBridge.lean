module
public import RustCrypto.Fors.Digest
public import RustCrypto.Fors.Window
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsDigest
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def nativeDigest (digest : Aeneas.Std.Array U8 34#usize) : EthLib.Cryptography.Sphincs.MessageDigest :=
  Vector.ofFn fun i => UInt8.ofNat (digest.val[i.val]'(by
    have hlen : digest.val.length = 34 := digest.property
    have hi : i.val < 34 := i.isLt
    omega)).val

theorem msb_bit_native (digest : Aeneas.Std.Array U8 34#usize) (p : Nat) (hp : p < 272) :
    EthLib.Cryptography.Sphincs.msbBit (nativeDigest digest) p =
      ((digest.val[p/8]!).val / 2^(7-p%8)) % 2 := by
  have hi : p/8 < digest.val.length := by
    have hl : digest.val.length = 34 := digest.property
    omega
  have hb : (digest.val[p/8]'hi).val < 256 := by scalar_tac
  have hi34 : p/8 < 34 := by omega
  have hget : (nativeDigest digest)[p/8]? = some ((nativeDigest digest)[p/8]'hi34) :=
    getElem?_pos (nativeDigest digest) (p/8) hi34
  rw [EthLib.Cryptography.Sphincs.msbBit,hget]
  simp only [nativeDigest,Vector.getElem_ofFn,Option.getD_some,UInt8.toNat_ofNat_of_lt' hb,
    Nat.shiftRight_eq_div_pow,getElem!_pos digest.val (p/8) hi]

theorem msb_bit_window (digest : Aeneas.Std.Array U8 34#usize) (start offset : Nat)
    (hstart : start+2 < 34) (hoffset : offset < 24) :
    EthLib.Cryptography.Sphincs.msbBit (nativeDigest digest) (8*start+offset) =
      windowBit (digest.val[start]!).val (digest.val[start+1]!).val (digest.val[start+2]!).val offset := by
  rw [msb_bit_native digest (8*start+offset) (by omega)]
  unfold windowBit
  split_ifs with hlow hmiddle
  · have hd : (8*start+offset)/8 = start := by omega
    have hm : (8*start+offset)%8 = offset := by omega
    rw [hd,hm]
  · have hd : (8*start+offset)/8 = start+1 := by omega
    have hm : 7-(8*start+offset)%8 = 15-offset := by omega
    rw [hd,hm]
  · have hd : (8*start+offset)/8 = start+2 := by omega
    have hm : 7-(8*start+offset)%8 = 23-offset := by omega
    rw [hd,hm]

theorem fold_values_agree (values : List Nat) (f g : Nat → Nat → Nat)
    (h : ∀ j ∈ values, ∀ value, f value j = g value j) (initial : Nat) :
    values.foldl f initial = values.foldl g initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    rw [h j (by simp)]
    exact ih (fun j hj value => h j (by simp [hj]) value) (g initial j)

theorem msb_field_window (digest : Aeneas.Std.Array U8 34#usize) (start offset : Nat)
    (hstart : start+2 < 34) (hoffset : offset < 8) :
    EthLib.Cryptography.Sphincs.msbField (nativeDigest digest) (8*start+offset) 10 =
      windowField (digest.val[start]!).val (digest.val[start+1]!).val (digest.val[start+2]!).val offset := by
  unfold EthLib.Cryptography.Sphincs.msbField windowField
  apply fold_values_agree
  intro j hj value
  have hj10 : j < 10 := List.mem_range.mp hj
  rw [Nat.add_assoc,msb_bit_window digest start (offset+j) hstart (by omega)]

/-- The source three-byte window is exactly the canonical ten-bit, most-significant-first digest field. -/
theorem selected_ethlib (digest : Aeneas.Std.Array U8 34#usize) (kappa : Nat) (hkappa : kappa < 24) :
    selected digest kappa = EthLib.Cryptography.Sphincs.msbField (nativeDigest digest) (10*kappa) 10 := by
  have hstart : kappa*10/8+2 < 34 := by omega
  have hoffset : kappa*10%8 < 8 := Nat.mod_lt _ (by decide)
  have hposition : 10*kappa = 8*(kappa*10/8)+kappa*10%8 := by omega
  rw [hposition,msb_field_window digest (kappa*10/8) (kappa*10%8) hstart hoffset,
    window_field_eq _ _ _ _ (by scalar_tac) (by scalar_tac) (by scalar_tac) hoffset]
  simp only [selected,Nat.shiftRight_eq_div_pow]

@[step] theorem leaf_position_ethlib_spec (digest : Aeneas.Std.Array U8 34#usize) (kappa : Usize)
    (hkappa : kappa.val < 24) :
    lean_sphincs.fors.leaf_position digest kappa ⦃ out =>
      out.val = kappa.val*1024 + EthLib.Cryptography.Sphincs.msbField (nativeDigest digest) (10*kappa.val) 10 ⦄ := by
  apply WP.spec_mono (leaf_position_spec digest kappa hkappa)
  intro out hout
  rw [hout,selected_ethlib digest kappa.val hkappa]

end RustCrypto.ForsDigest
