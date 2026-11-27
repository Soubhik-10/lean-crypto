module
public import RustCrypto.Wots.Encoding.Codeword
public import EthLib.Cryptography.Sphincs.Encoding
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Codeword

/-- Preserve the sixteen source bytes in EthLib's fixed-length digest type. -/
def asDigest (code : Aeneas.Std.Array U8 16#usize) : EthLib.Cryptography.Sphincs.Digest :=
  Vector.ofFn fun i => UInt8.ofNat (code.val[i.val]'(by
    have hlen : code.val.length = 16 := code.property
    have hi : i.val < 16 := by simpa [EthLib.Cryptography.Sphincs.Constants.N] using i.isLt
    omega)).val

theorem digit_ethlib (code : Aeneas.Std.Array U8 16#usize) (i : Fin 64) :
    digitAt code i.val =
      ((EthLib.Cryptography.Sphincs.Internal.digits (asDigest code))[i.val]'
        (by exact i.isLt)).val := by
  have hindex : i.val / 4 < code.val.length := by
    have hlen : code.val.length = 16 := code.property
    have hi := i.isLt
    omega
  have hbyte : (code.val[i.val / 4]'hindex).val < 256 := by scalar_tac
  simp only [digitAt, getElem?_pos code.val (i.val / 4) hindex, Option.getD_some,
    EthLib.Cryptography.Sphincs.Internal.digits, Vector.getElem_ofFn,
    asDigest, UInt8.toNat_ofNat_of_lt' hbyte]

theorem digit_array_ethlib (code : Aeneas.Std.Array U8 16#usize) :
    (expectedDigits code).val.map UScalar.val =
      (EthLib.Cryptography.Sphincs.Internal.digits (asDigest code)).toList.map Fin.val := by
  apply List.ext_getElem
  · simp [EthLib.Cryptography.Sphincs.Constants.V]
    exact Vector.length_toList
  · intro i hi hother
    have hi64 : i < 64 := by simpa using hi
    have hvalue := expected_digit code i hi64
    have hindex : i < (expectedDigits code).val.length := by simpa using hi64
    rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos (expectedDigits code).val i hindex] at hvalue
    simp only [List.getElem_map]
    exact hvalue.trans (by simpa using digit_ethlib code ⟨i, hi64⟩)

theorem digit_sum_ethlib (code : Aeneas.Std.Array U8 16#usize) :
    sumPrefix (expectedDigits code) 64 =
      EthLib.Cryptography.Sphincs.Internal.digitSum
        (EthLib.Cryptography.Sphincs.Internal.digits (asDigest code)) := by
  have ht : (expectedDigits code).val.take 64 = (expectedDigits code).val :=
    List.take_of_length_le (by simp)
  simp only [sumPrefix, ht]
  rw [digit_array_ethlib]
  simp only [EthLib.Cryptography.Sphincs.Internal.digitSum, List.sum_eq_foldl,
    List.foldl_map, Vector.foldl_toList]

/-- Complete source-to-EthLib refinement of the WOTS+C codeword decision. -/
@[step] theorem codeword_ethlib_spec (code : Aeneas.Std.Array U8 16#usize) :
    lean_sphincs.wots.codeword code ⦃ out =>
      out.map (fun digits => digits.val.map UScalar.val) =
        (EthLib.Cryptography.Sphincs.codeword? (asDigest code)).map
          (fun digits => digits.toList.map Fin.val) ⦄ := by
  apply WP.spec_mono (codeword_spec code)
  intro out hout
  rw [hout]
  have hs := digit_sum_ethlib code
  simp only [EthLib.Cryptography.Sphincs.codeword?, ← hs,
    EthLib.Cryptography.Sphincs.Constants.TARGET_SUM]
  by_cases h : sumPrefix (expectedDigits code) 64 = 128
  · simp [h, digit_array_ethlib]
  · simp [h]

end RustCrypto.Codeword
