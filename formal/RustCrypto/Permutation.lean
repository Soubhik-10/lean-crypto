module
public import LeanSphincs.Funs
public import RustCrypto.SimdRound
public import RustCrypto.RoundConstants
public import Batching.Keccak
public import Mathlib.Tactic.FinCases
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Permutation
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384


abbrev width := 2
abbrev Word := wide.u64x2_.u64x2

theorem width_matches_source : width = lean_sphincs.hash.batch.WIDTH.val := by
  simp only [lean_sphincs.hash.batch.WIDTH]
  rfl
abbrev State := Aeneas.Std.Array Word 25#usize

def wordAt {n : Usize} (state : Aeneas.Std.Array Word n) (i : Nat) : Word := state[i]!

def parity (state : State) (x : Nat) : Word := fun lane =>
  wordAt state x lane ^^^ wordAt state (x+5) lane ^^^ wordAt state (x+10) lane ^^^
    wordAt state (x+15) lane ^^^ wordAt state (x+20) lane

@[step] theorem xor_spec (a b : Word) :
    wide.u64x2_.u64x2.Insts.CoreOpsBitBitXoru64x2u64x2.bitxor a b ⦃ out =>
      out = fun lane => a lane ^^^ b lane ⦄ := by simp [wide.u64x2_.u64x2.Insts.CoreOpsBitBitXoru64x2u64x2.bitxor, WP.spec_ok]

@[step] theorem parity_call_spec (state : State) (index : Usize) (hi : index.val < 5) :
    lean_sphincs.hash.batch.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
      state index ⦃ out => out.1 = parity state index.val ∧ out.2 = state ⦄ := by
  unfold lean_sphincs.hash.batch.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
  step*
  funext lane
  simp_all [parity, wordAt, Aeneas.Std.Array.getElem!_Nat_eq]
  simp (disch := scalar_tac) only [getElem?_pos, Option.getD_some]


def rotateWord (n : Nat) (word : Word) : Word := fun lane => ⟨(word lane).bv.rotateLeft n⟩

@[step] theorem rotate_value_spec (angle : U32) (word : Word) (ha : angle.val < 64) :
    lean_sphincs.hash.batch.rotate angle word ⦃ out => out = rotateWord angle.val word ⦄ := by
  apply WP.spec_mono (RustCrypto.SimdRound.rotate_spec angle word ha)
  intro out hout
  funext lane
  exact congrArg (fun bv : BitVec 64 => (⟨bv⟩ : U64)) (hout lane)

def theta (columns : Aeneas.Std.Array Word 5#usize) (x : Nat) : Word := fun lane =>
  wordAt columns ((x+4)%5) lane ^^^ rotateWord 1 (wordAt columns ((x+1)%5)) lane

@[step] theorem theta_call_spec (columns : Aeneas.Std.Array Word 5#usize) (index : Usize)
    (hi : index.val < 5) :
    lean_sphincs.hash.batch.permute.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
      columns index ⦃ out => out.1 = theta columns index.val ∧ out.2 = columns ⦄ := by
  unfold lean_sphincs.hash.batch.permute.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
  step*
  funext lane
  simp_all [theta, wordAt, Aeneas.Std.Array.getElem!_Nat_eq]
  simp (disch := scalar_tac) only [getElem?_pos, Option.getD_some]

@[step] theorem and_spec (a b : Word) :
    wide.u64x2_.u64x2.Insts.CoreOpsBitBitAndu64x2u64x2.bitand a b ⦃ out =>
      out = fun lane => a lane &&& b lane ⦄ := by
  simp [wide.u64x2_.u64x2.Insts.CoreOpsBitBitAndu64x2u64x2.bitand, WP.spec_ok]

@[step] theorem not_spec (a : Word) :
    wide.u64x2_.u64x2.Insts.CoreOpsBitNotu64x2.not a ⦃ out =>
      out = fun lane => ~~~(a lane) ⦄ := by
  simp [wide.u64x2_.u64x2.Insts.CoreOpsBitNotu64x2.not, WP.spec_ok]

def chi (rotated : State) (i : Nat) : Word := fun lane =>
  wordAt rotated i lane ^^^ (~~~(wordAt rotated (i/5*5+(i%5+1)%5) lane) &&&
    wordAt rotated (i/5*5+(i%5+2)%5) lane)

@[step] theorem chi_call_spec (rotated : State) (index : Usize) (hi : index.val < 25) :
    lean_sphincs.hash.batch.permute.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
      rotated index ⦃ out => out.1 = chi rotated index.val ∧ out.2 = rotated ⦄ := by
  unfold lean_sphincs.hash.batch.permute.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2.call_mut
  step*
  funext lane
  simp_all [chi, wordAt, Aeneas.Std.Array.getElem!_Nat_eq]
  simp (disch := scalar_tac) only [getElem?_pos, Option.getD_some]
  rfl


def tabulate (n : Usize) (fn : Nat → Word) : Aeneas.Std.Array Word n :=
  Aeneas.Std.Array.from (List.ofFn fun i : Fin n.val => fn i.val) (by simp)

@[simp] theorem wordAt_tabulate (n : Usize) (fn : Nat → Word) (i : Nat) (hi : i < n.val) :
    wordAt (tabulate n fn) i = fn i := by
  unfold wordAt
  rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos (tabulate n fn).val i (by simpa using hi)]
  simp only [tabulate, Aeneas.Std.Array.from_val, List.getElem_ofFn]

theorem from_fn_exact {F : Type} (n : Usize) (cb : core.ops.function.FnMut F Usize Word)
    (state : F) (fn : Nat → Word)
    (h : ∀ i : Usize, i.val < n.val → cb.call_mut state i ⦃ out =>
      out.1 = fn i.val ∧ out.2 = state ⦄) :
    core.array.from_fn n cb state ⦃ out => out = tabulate n fn ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! n cb state
    (fun i value => value = fn i) h)
  intro out hout
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp
  · intro i hi hother
    have hv := hout i (by simpa using hi)
    rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos out.val i hi] at hv
    simpa only [tabulate, Aeneas.Std.Array.from_val, List.getElem_ofFn] using hv

@[step] theorem parity_array_spec (state : State) :
    core.array.from_fn 5#usize
      lean_sphincs.hash.batch.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2 state ⦃ out =>
        out = tabulate 5#usize (parity state) ⦄ := by
  apply from_fn_exact
  intro i hi
  exact parity_call_spec state i (by simpa using hi)

@[step] theorem theta_array_spec (columns : Aeneas.Std.Array Word 5#usize) :
    core.array.from_fn 5#usize
      lean_sphincs.hash.batch.permute.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2 columns ⦃ out =>
        out = tabulate 5#usize (theta columns) ⦄ := by
  apply from_fn_exact
  intro i hi
  exact theta_call_spec columns i (by simpa using hi)

@[step] theorem chi_array_spec (rotated : State) :
    core.array.from_fn 25#usize
      lean_sphincs.hash.batch.permute.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeu64x2 rotated ⦃ out =>
        out = tabulate 25#usize (chi rotated) ⦄ := by
  apply from_fn_exact
  intro i hi
  exact chi_call_spec rotated i (by simpa using hi)


@[step] theorem xor_assign_spec (a b : Word) :
    wide.u64x2_.u64x2.Insts.CoreOpsBitBitXorAssignu64x2.bitxor_assign a b ⦃ out =>
      out = fun lane => a lane ^^^ b lane ⦄ := by
  simp [wide.u64x2_.u64x2.Insts.CoreOpsBitBitXorAssignu64x2.bitxor_assign, WP.spec_ok]

@[step] theorem new_spec (a : Aeneas.Std.Array U64 2#usize) :
    wide.u64x2_.u64x2.new a ⦃ out => out = fun lane => a[lane.val]! ⦄ := by
  simp only [wide.u64x2_.u64x2.new, WP.spec_ok]
  funext lane
  rw [Aeneas.Std.Array.getElem!_Nat_eq, getElem!_pos a.val lane.val (by
    have hi := lane.isLt
    scalar_tac)]

def rhoPi (state : State) : State :=
  let corrections := tabulate 5#usize (theta (tabulate 5#usize (parity state)))
  Aeneas.Std.Array.make 25#usize [
    rotateWord 0 (fun lane => wordAt state 0 lane ^^^ wordAt corrections 0 lane),
    rotateWord 44 (fun lane => wordAt state 6 lane ^^^ wordAt corrections 1 lane),
    rotateWord 43 (fun lane => wordAt state 12 lane ^^^ wordAt corrections 2 lane),
    rotateWord 21 (fun lane => wordAt state 18 lane ^^^ wordAt corrections 3 lane),
    rotateWord 14 (fun lane => wordAt state 24 lane ^^^ wordAt corrections 4 lane),
    rotateWord 28 (fun lane => wordAt state 3 lane ^^^ wordAt corrections 3 lane),
    rotateWord 20 (fun lane => wordAt state 9 lane ^^^ wordAt corrections 4 lane),
    rotateWord 3 (fun lane => wordAt state 10 lane ^^^ wordAt corrections 0 lane),
    rotateWord 45 (fun lane => wordAt state 16 lane ^^^ wordAt corrections 1 lane),
    rotateWord 61 (fun lane => wordAt state 22 lane ^^^ wordAt corrections 2 lane),
    rotateWord 1 (fun lane => wordAt state 1 lane ^^^ wordAt corrections 1 lane),
    rotateWord 6 (fun lane => wordAt state 7 lane ^^^ wordAt corrections 2 lane),
    rotateWord 25 (fun lane => wordAt state 13 lane ^^^ wordAt corrections 3 lane),
    rotateWord 8 (fun lane => wordAt state 19 lane ^^^ wordAt corrections 4 lane),
    rotateWord 18 (fun lane => wordAt state 20 lane ^^^ wordAt corrections 0 lane),
    rotateWord 27 (fun lane => wordAt state 4 lane ^^^ wordAt corrections 4 lane),
    rotateWord 36 (fun lane => wordAt state 5 lane ^^^ wordAt corrections 0 lane),
    rotateWord 10 (fun lane => wordAt state 11 lane ^^^ wordAt corrections 1 lane),
    rotateWord 15 (fun lane => wordAt state 17 lane ^^^ wordAt corrections 2 lane),
    rotateWord 56 (fun lane => wordAt state 23 lane ^^^ wordAt corrections 3 lane),
    rotateWord 62 (fun lane => wordAt state 2 lane ^^^ wordAt corrections 2 lane),
    rotateWord 55 (fun lane => wordAt state 8 lane ^^^ wordAt corrections 3 lane),
    rotateWord 39 (fun lane => wordAt state 14 lane ^^^ wordAt corrections 4 lane),
    rotateWord 41 (fun lane => wordAt state 15 lane ^^^ wordAt corrections 0 lane),
    rotateWord 2 (fun lane => wordAt state 21 lane ^^^ wordAt corrections 1 lane)
  ]

def roundModel (constant : U64) (state : State) : State :=
  let nonlinear := tabulate 25#usize (chi (rhoPi state))
  nonlinear.set 0#usize (fun lane => wordAt nonlinear 0 lane ^^^ constant)

@[step] theorem round_body_spec (state : State) (round : Usize) (hr : round.val < 24) :
    lean_sphincs.hash.batch.permute_loop.body state round ⦃ out =>
      match out with
      | .cont (next, nextRound) =>
          next = roundModel (RustCrypto.RoundConstants.constantArray[round.val]!) state ∧
          nextRound.val = round.val + 1
      | .done _ => False ⦄ := by
  unfold lean_sphincs.hash.batch.permute_loop.body
  have hbranch : round < lean_sphincs.hash.batch.ROUNDS := by
    simpa only [lean_sphincs.hash.batch.ROUNDS] using (show round < 24#usize by scalar_tac)
  simp only [ite_eq_left hbranch]
  step*
  simp_all [roundModel, rhoPi, wordAt, Aeneas.Std.Array.getElem!_Nat_eq]
  simp_all
  congr 1
  funext lane
  fin_cases lane <;> rfl

end RustCrypto.Permutation
