module
public import LeanSphincs.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Codeword
set_option maxHeartbeats 1000000

def digitAt (code : Aeneas.Std.Array U8 16#usize) (i : Nat) : Nat :=
  (((code.val[i / 4]?).getD 0#u8).val >>> (6 - 2 * (i % 4))) % 4

@[step] theorem extract_digit_spec (code : Aeneas.Std.Array U8 16#usize) (index : Usize)
    (hi : index.val < 64) :
    lean_sphincs.wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      code index ⦃ out => out.1.val = digitAt code index.val ∧
        out.1.val < 4 ∧ out.2 = code ⦄ := by
  unfold lean_sphincs.wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  simp only [alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndex.index,
    lean_sphincs.core.ops.index.IndexArray, Aeneas.Std.core.ops.index.IndexArray,
    core.array.Array.index, core.ops.index.IndexSlice,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Slice.index, core.slice.index.Usize.index]
  have hindex : index.val / 4 < code.val.length := by
    have hlen : code.val.length = 16 := code.property
    omega
  step*
  have mask (value : Nat) : value &&& 3 = value % 4 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod value 2
  simp_all [digitAt, UScalar.val_and]
  exact Nat.mod_lt _ (by decide : 0 < 4)

/-- All 64 source-extracted digits have their specified values and bounds. -/
@[step] theorem digits_spec (code : Aeneas.Std.Array U8 16#usize) :
    core.array.from_fn 64#usize
      lean_sphincs.wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 code ⦃ out =>
        ∀ i < 64, (out[i]!).val = digitAt code i ∧ (out[i]!).val < 4 ⦄ := by
  apply core.array.from_fn.spec_stateless_getElem! 64#usize
    lean_sphincs.wots.codeword.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 code
    (fun i value => value.val = digitAt code i ∧ value.val < 4)
  intro index hindex
  apply WP.spec_mono (extract_digit_spec code index (by simpa using hindex))
  rintro ⟨value, state⟩ ⟨heq, hlt, hstate⟩
  exact ⟨⟨heq, hlt⟩, hstate⟩

def sumPrefix (digits : Aeneas.Std.Array U8 64#usize) (count : Nat) : Nat :=
  ((digits.val.take count).map UScalar.val).sum

theorem sum_prefix_succ (digits : Aeneas.Std.Array U8 64#usize) (i : Nat) (hi : i < 64) :
    sumPrefix digits (i + 1) = sumPrefix digits i + (digits[i]!).val := by
  have hindex : i < digits.val.length := by simpa using hi
  unfold sumPrefix
  rw [List.take_succ_eq_append_getElem hindex]
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  simp only [Aeneas.Std.Array.getElem!_Nat_eq]
  rw [getElem!_pos digits.val i hindex]

theorem sum_prefix_bound (digits : Aeneas.Std.Array U8 64#usize)
    (bounds : ∀ i < 64, (digits[i]!).val < 4) (count : Nat) (hc : count ≤ 64) :
    sumPrefix digits count ≤ 3 * count := by
  induction count with
  | zero => simp [sumPrefix]
  | succ count ih =>
    rw [sum_prefix_succ digits count (by omega)]
    have hdigit := bounds count (by omega)
    have hprev := ih (by omega)
    omega

@[step] theorem widen_byte_spec (value : U8) :
    lift (core.convert.num.FromU16U8.from value) ⦃ out => out.val = value.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact core.convert.num.FromU16U8.from_val_eq value

/-- The actual target-sum loop is total and computes the natural-number digit sum. -/
@[step] theorem sum_loop_spec (digits : Aeneas.Std.Array U8 64#usize)
    (bounds : ∀ i < 64, (digits[i]!).val < 4) (sum : U16) (index : Usize)
    (hi : index.val ≤ 64) (hs : sum.val = sumPrefix digits index.val) :
    lean_sphincs.wots.codeword_loop digits sum index ⦃ out =>
      out.val = sumPrefix digits 64 ⦄ := by
  unfold lean_sphincs.wots.codeword_loop
  apply loop.spec_decr_nat
    (fun state : U16 × Usize => 64 - state.2.val)
    (fun state : U16 × Usize => state.2.val ≤ 64 ∧
      state.1.val = sumPrefix digits state.2.val)
  · rintro ⟨current, j⟩ ⟨hj, hcurrent⟩
    dsimp only at hj hcurrent
    dsimp only
    have hsum : current.val ≤ 3 * j.val :=
      hcurrent.trans_le (sum_prefix_bound digits bounds j.val hj)
    unfold lean_sphincs.wots.codeword_loop.body
    simp only [lean_sphincs.params.WOTS_CHAINS]
    by_cases hrun : j.val < 64
    · have hbranch : j < 64#usize := by scalar_tac
      have hindex : j.val < digits.val.length := by simpa using hrun
      have hdigit := bounds j.val hrun
      rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos digits.val j.val hindex] at hdigit
      simp only [ite_eq_left hbranch]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [i3_post, sum_prefix_succ digits j.val hrun]
      simp_all
    · have hstop : ¬ j < 64#usize := by scalar_tac
      have hdone : j.val = 64 := by omega
      simpa [hstop, WP.spec_ok, hdone] using hcurrent
  · exact ⟨hi, hs⟩

def expectedDigits (code : Aeneas.Std.Array U8 16#usize) : Aeneas.Std.Array U8 64#usize :=
  Aeneas.Std.Array.from (List.ofFn fun index : Fin 64 =>
    U8.ofNatCore (digitAt code index.val) (by
      have h : digitAt code index.val < 4 := Nat.mod_lt _ (by decide : 0 < 4)
      change digitAt code index.val < 256
      omega)) (by simp)

theorem expected_digit (code : Aeneas.Std.Array U8 16#usize) (i : Nat) (hi : i < 64) :
    ((expectedDigits code)[i]!).val = digitAt code i := by
  have hindex : i < (expectedDigits code).val.length := by simpa using hi
  rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos (expectedDigits code).val i hindex]
  simp only [expectedDigits, Aeneas.Std.Array.from_val, List.getElem_ofFn, U8.ofNatCore,
    UScalar.ofNatCore_val_eq]

theorem digits_unique (code : Aeneas.Std.Array U8 16#usize) (digits : Aeneas.Std.Array U8 64#usize)
    (h : ∀ i < 64, (digits[i]!).val = digitAt code i) : digits = expectedDigits code := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp
  · intro i hi hother
    apply UScalar.eq_of_val_eq
    have hvalue := h i (by simpa using hi)
    have hexpected := expected_digit code i (by simpa using hi)
    rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos digits.val i hi] at hvalue
    rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos (expectedDigits code).val i hother] at hexpected
    exact hvalue.trans hexpected.symm

/-- The source accepts exactly the words whose 64 decoded digits sum to 128. -/
@[step] theorem codeword_spec (code : Aeneas.Std.Array U8 16#usize) :
    lean_sphincs.wots.codeword code ⦃ out =>
      out = if sumPrefix (expectedDigits code) 64 = 128 then some (expectedDigits code) else none ⦄ := by
  unfold lean_sphincs.wots.codeword
  step with digits_spec as ⟨digits, hdigits⟩
  have heq : digits = expectedDigits code := digits_unique code digits (fun i hi => (hdigits i hi).1)
  step with sum_loop_spec digits (fun i hi => (hdigits i hi).2) 0#u16 0#usize (by simp)
    (by simp [sumPrefix])
  simp_all [lean_sphincs.params.TARGET_SUM, UScalar.eq_equiv]
  split <;> simp_all [WP.spec_ok]

end RustCrypto.Codeword
