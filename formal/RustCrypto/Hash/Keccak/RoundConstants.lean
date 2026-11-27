module
public import LeanSphincs.Funs
public import EthLib.Cryptography.Hash.Keccak
import all Aeneas.Std.Scalar.Ops.Add
import all Aeneas.Std.Scalar.Ops.Sub
import all Aeneas.Std.Scalar.Bitwise
public import Mathlib.Tactic.IntervalCases
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.RoundConstants
set_option maxHeartbeats 2000000

@[step] theorem shift_one_spec (j : I32) (h0 : 0 ≤ j.val) (h6 : j.val ≤ 6) :
    (1#i32 <<< j) ⦃ out => out.val = (2 : Int) ^ j.toNat ⦄ := by
  apply WP.spec_mono (I32.ShiftLeft_IScalar_spec (1#i32) j h0 (by omega))
  rintro out ⟨hval, _⟩
  interval_cases hj : j.val <;>
    simpa [Int.shiftLeft_eq, IScalar.toNat, hj, I32.size, I32.numBits] using hval

@[step] theorem bits_body_done (round : Usize) (constants : Aeneas.Std.Array U64 24#usize)
    (lfsr : U8) (j : I32) (hj : 7 ≤ j.val) :
    lean_sphincs.hash.batch.round_constants_loop0_loop0.body round constants lfsr j ⦃ result =>
      result = .done (constants, lfsr) ⦄ := by
  have hstop : ¬ j < 7#i32 := by scalar_tac
  simp [lean_sphincs.hash.batch.round_constants_loop0_loop0.body, hstop, WP.spec_ok]

def mask (j : Nat) (lfsr : U8) : BitVec 64 :=
  (lfsr.bv &&& 1#8).setWidth 64 <<< (((2 : Int) ^ j - 1).toNat)

def lfStep (lfsr : U8) : U8 :=
  ⟨(lfsr.bv <<< 1) ^^^ (if lfsr.val &&& 128 = 0 then 0#8 else 113#8)⟩

@[step] theorem bits_body_spec (round : Usize) (constants : Aeneas.Std.Array U64 24#usize)
    (lfsr : U8) (j : I32) (hr : round.val < 24) (hj0 : 0 ≤ j.val) (hj7 : j.val < 7) :
    lean_sphincs.hash.batch.round_constants_loop0_loop0.body round constants lfsr j ⦃ result =>
      match result with
      | .cont (nextConstants, nextLfsr, nextJ) =>
          nextConstants.val.map UScalar.bv = (constants.val.map UScalar.bv).set round.val
            ((constants.val[round.val]'(by simpa using hr)).bv ||| mask j.toNat lfsr) ∧
          nextLfsr.bv = (lfStep lfsr).bv ∧ nextJ.val = j.val + 1
      | .done _ => False ⦄ := by
  have hp0 : (0 : Int) < 2 ^ j.toNat := by positivity
  have hjn : j.toNat ≤ 6 := by scalar_tac
  have hp6 : (2 : Int) ^ j.toNat ≤ 64 := by
    calc
      (2 : Int) ^ j.toNat ≤ 2 ^ 6 := pow_le_pow_right₀ (by decide) hjn
      _ = 64 := by norm_num
  have hbranch : j < 7#i32 := by scalar_tac
  unfold lean_sphincs.hash.batch.round_constants_loop0_loop0.body
  simp only [ite_eq_left hbranch]
  step*
  have hcast : i1.bv = (lfsr.bv &&& 1#8).setWidth 64 := by
    rw [i1_post]
    change i.bv.setWidth 64 = (lfsr.bv &&& 1#8).setWidth 64
    exact congrArg (fun bits : BitVec 8 => bits.setWidth 64) i_post1
  have hmask : UScalar.bv i4 = mask j.toNat lfsr := by
    rw [i4_post1]
    change i1.bv <<< (i3.val).toNat = _
    rw [hcast]
    simp only [mask, I32.toNat, i3_post, i2_post]
  have harray : a.val.map UScalar.bv = (constants.val.map UScalar.bv).set round.val
      ((constants.val[round.val]'(by simpa using hr)).bv ||| mask j.toNat lfsr) := by
    rw [a_post, Aeneas.Std.Array.set_val_eq, List.map_set]
    rw [i6_post1, i5_post]
    have hmask64 : i4.bv = mask j.toNat lfsr := hmask
    exact congrArg (fun bits : BitVec 64 => (constants.val.map U64.bv).set round.val
      ((constants.val[round.val]'(by simpa using hr)).bv ||| bits)) hmask64
  have hfeedback : i7.val = lfsr.val &&& 128 := by simpa [UScalar.val_and] using i7_post
  split
  · step*
    refine ⟨harray, ?_, j1_post⟩
    have hhigh : lfsr.val &&& 128 ≠ 0 := by scalar_tac
    simp only [lfStep, ite_eq_right hhigh]
    have hlf : lfsr1.bv = i8.bv ^^^ (113 : BitVec 8) := lfsr1_post1
    have hshift : i8.bv = lfsr.bv <<< 1 := i8_post1
    change lfsr1.bv = (lfsr.bv <<< 1) ^^^ 113#8
    rw [hlf, hshift]
    congr 1
  · step*
    refine ⟨harray, ?_, j1_post⟩
    have hhigh : lfsr.val &&& 128 = 0 := by scalar_tac
    simp only [lfStep, ite_eq_left hhigh]
    have hlf : lfsr1.bv = i8.bv ^^^ (0 : BitVec 8) := lfsr1_post1
    have hshift : i8.bv = lfsr.bv <<< 1 := i8_post1
    change lfsr1.bv = (lfsr.bv <<< 1) ^^^ 0#8
    rw [hlf, hshift]
    congr 1


def bits : Nat → Nat → Nat → U8 → List (BitVec 64) → List (BitVec 64) × U8
  | 0, _, _, lfsr, words => (words, lfsr)
  | fuel + 1, j, round, lfsr, words =>
      bits fuel (j + 1) round (lfStep lfsr)
        (words.set round ((words[round]?).getD 0#64 ||| mask j lfsr))

@[step] theorem bits_loop_spec (round : Usize) (hr : round.val < 24)
    (constants : Aeneas.Std.Array U64 24#usize) (lfsr : U8) (j : I32)
    (hj0 : 0 ≤ j.val) (hj7 : j.val ≤ 7) :
    lean_sphincs.hash.batch.round_constants_loop0_loop0 constants lfsr round j ⦃ out =>
      (out.1.val.map UScalar.bv, out.2) =
        bits (7 - j.toNat) j.toNat round.val lfsr (constants.val.map UScalar.bv) ⦄ := by
  let expected := bits (7 - j.toNat) j.toNat round.val lfsr (constants.val.map UScalar.bv)
  unfold lean_sphincs.hash.batch.round_constants_loop0_loop0
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array U64 24#usize × U8 × I32 => 7 - state.2.2.toNat)
    (fun state : Aeneas.Std.Array U64 24#usize × U8 × I32 =>
      0 ≤ state.2.2.val ∧ state.2.2.val ≤ 7 ∧
        expected = bits (7 - state.2.2.toNat) state.2.2.toNat round.val
          state.2.1 (state.1.val.map UScalar.bv))
  · rintro ⟨current, lf, cj⟩ ⟨hc0, hc7, hmodel⟩
    dsimp only at hc0 hc7 hmodel
    dsimp only
    by_cases hrun : cj.val < 7
    · apply WP.spec_mono (bits_body_spec round current lf cj hr hc0 hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextConstants, nextLfsr, nextJ⟩
        rcases hresult with ⟨harray, hlf, hjnext⟩
        have hnext : nextJ.toNat = cj.toNat + 1 := by scalar_tac
        have hlf' : nextLfsr = lfStep lf := by
          exact congrArg (fun bv : BitVec 8 => (⟨bv⟩ : U8)) hlf
        have hget : ((current.val.map UScalar.bv)[round.val]?).getD 0#64 =
            (current.val[round.val]'(by simpa using hr)).bv := by
          rw [getElem?_pos (current.val.map UScalar.bv) round.val (by simpa using hr)]
          simp only [Option.getD_some, List.getElem_map]
        refine ⟨⟨by scalar_tac, by scalar_tac, ?_⟩, by scalar_tac⟩
        rw [hmodel]
        have hf : 7 - cj.toNat = (7 - (cj.toNat + 1)) + 1 := by scalar_tac
        rw [hf, bits]
        simp only [hnext, hlf', harray, hget]
    · apply WP.spec_mono (bits_body_done round current lf cj (by omega))
      intro result hresult
      subst result
      have hdone : cj.toNat = 7 := by scalar_tac
      simpa only [hdone, Nat.sub_self, bits] using hmodel.symm
  · exact ⟨hj0, hj7, rfl⟩


def rounds : Nat → Nat → U8 → List (BitVec 64) → List (BitVec 64)
  | 0, _, _, words => words
  | fuel + 1, round, lfsr, words =>
      let next := bits 7 0 round lfsr words
      rounds fuel (round + 1) next.2 next.1

@[step] theorem rounds_loop_spec (constants : Aeneas.Std.Array U64 24#usize)
    (lfsr : U8) (round : Usize) (hr : round.val ≤ 24) :
    lean_sphincs.hash.batch.round_constants_loop0 constants lfsr round ⦃ out =>
      out.val.map UScalar.bv = rounds (24 - round.val) round.val lfsr
        (constants.val.map UScalar.bv) ⦄ := by
  let expected := rounds (24 - round.val) round.val lfsr (constants.val.map UScalar.bv)
  unfold lean_sphincs.hash.batch.round_constants_loop0
  apply loop.spec_decr_nat
    (fun state : Aeneas.Std.Array U64 24#usize × U8 × Usize => 24 - state.2.2.val)
    (fun state : Aeneas.Std.Array U64 24#usize × U8 × Usize =>
      state.2.2.val ≤ 24 ∧ expected = rounds (24 - state.2.2.val) state.2.2.val
        state.2.1 (state.1.val.map UScalar.bv))
  · rintro ⟨current, lf, cr⟩ ⟨hcr, hmodel⟩
    dsimp only at hcr hmodel
    dsimp only
    unfold lean_sphincs.hash.batch.round_constants_loop0.body
    simp only [lean_sphincs.hash.batch.ROUNDS]
    split
    · step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hmodel]
      have hf : 24 - cr.val = (24 - (cr.val + 1)) + 1 := by scalar_tac
      rw [hf, rounds]
      have hpair : (constants1.val.map UScalar.bv, lfsr1) =
          bits 7 0 cr.val lf (current.val.map UScalar.bv) := by simpa using constants1_post
      rw [← hpair]
      simp only [round1_post]
    · step*
      have hdone : cr.val = 24 := by scalar_tac
      simpa [hdone, rounds] using hmodel.symm
  · exact ⟨hr, rfl⟩

@[step] theorem round_constants_spec : lean_sphincs.hash.batch.round_constants ⦃ out =>
    out.val.map UScalar.bv = rounds 24 0 1#u8 (List.replicate 24 0#64) ⦄ := by
  unfold lean_sphincs.hash.batch.round_constants
  step*
  simpa using out_post

/-- Closed table comparison is evaluated by Lean's kernel. -/
theorem model_table_eq : rounds 24 0 1#u8 (List.replicate 24 0#64) =
    EthLib.Cryptography.Hash.Keccak.RC.toList.map UInt64.toBitVec := by decide

/-- Actual Rust-generated round constants, entry for entry, match EthLib. -/
@[step] theorem round_table_spec : lean_sphincs.hash.batch.ROUND_CONSTANTS ⦃ out =>
    out.val.map UScalar.bv =
      EthLib.Cryptography.Hash.Keccak.RC.toList.map UInt64.toBitVec ⦄ := by
  unfold lean_sphincs.hash.batch.ROUND_CONSTANTS
  apply WP.spec_mono round_constants_spec
  intro out hout
  exact hout.trans model_table_eq


def constantArray : Aeneas.Std.Array U64 24#usize :=
  Aeneas.Std.Array.from
    (EthLib.Cryptography.Hash.Keccak.RC.toList.map (fun word => (⟨word.toBitVec⟩ : U64))) (by rw [List.length_map, Vector.length_toList]; rfl)

@[step] theorem round_table_exact_spec : lean_sphincs.hash.batch.ROUND_CONSTANTS ⦃ out =>
    out = constantArray ⦄ := by
  apply WP.spec_mono round_table_spec
  intro out hout
  apply Aeneas.Std.Array.ext
  have h := congrArg (List.map (fun bv : BitVec 64 => (⟨bv⟩ : U64))) hout
  simp only [List.map_map] at h
  change List.map (fun x : U64 => (⟨UScalar.bv x⟩ : U64)) out.val = constantArray.val at h
  have heta : (fun x : U64 => (⟨UScalar.bv x⟩ : U64)) = id := by
    funext x
    cases x
    rfl
  rw [heta, List.map_id] at h
  exact h

end RustCrypto.RoundConstants
