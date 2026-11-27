module
public import LeanSphincs.Funs
public import RustCrypto.Hash.Keccak.Rotate
public import RustCrypto.Hash.Keccak.RoundConstants
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

/-- One lane of the source helper, retaining all checked index arithmetic. -/
def chiElement (rotated : State) (index : Usize) : Result Word := do
  let ux ← Aeneas.Std.Array.index_usize rotated index
  let row ← index / 5#usize
  let base ← row * 5#usize
  let plusOne ← index + 1#usize
  let next ← plusOne % 5#usize
  let first ← base + next
  let ux1 ← Aeneas.Std.Array.index_usize rotated first
  let ux2 ← wide.u64x2_.u64x2.Insts.CoreOpsBitNotu64x2.not ux1
  let baseAgain ← row * 5#usize
  let plusTwo ← index + 2#usize
  let nextTwo ← plusTwo % 5#usize
  let second ← baseAgain + nextTwo
  let ux3 ← Aeneas.Std.Array.index_usize rotated second
  let ux4 ← wide.u64x2_.u64x2.Insts.CoreOpsBitBitAndu64x2u64x2.bitand ux2 ux3
  wide.u64x2_.u64x2.Insts.CoreOpsBitBitXoru64x2u64x2.bitxor ux ux4

@[step] theorem chiElement_spec (rotated : State) (index : Usize) (hi : index.val < 25) :
    chiElement rotated index ⦃ out => out = chi rotated index.val ⦄ := by
  unfold chiElement
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

/-- Constant lane expressions enumerate the same 25 entries as the existing tabulation model. -/
theorem literal25_tabulate (fn : Nat → Word) :
    Aeneas.Std.Array.make 25#usize [
      fn 0, fn 1, fn 2, fn 3, fn 4,
      fn 5, fn 6, fn 7, fn 8, fn 9,
      fn 10, fn 11, fn 12, fn 13, fn 14,
      fn 15, fn 16, fn 17, fn 18, fn 19,
      fn 20, fn 21, fn 22, fn 23, fn 24] = tabulate 25#usize fn := by
  apply Aeneas.Std.Array.ext
  simp only [Aeneas.Std.Array.make_val, tabulate, Aeneas.Std.Array.from_val]
  rfl

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

/-- Factoring the extracted helper into its 25 checked lane computations. -/
def chiElements (rotated : State) : Result State := do
  let lane0 ← chiElement rotated 0#usize
  let lane1 ← chiElement rotated 1#usize
  let lane2 ← chiElement rotated 2#usize
  let lane3 ← chiElement rotated 3#usize
  let lane4 ← chiElement rotated 4#usize
  let lane5 ← chiElement rotated 5#usize
  let lane6 ← chiElement rotated 6#usize
  let lane7 ← chiElement rotated 7#usize
  let lane8 ← chiElement rotated 8#usize
  let lane9 ← chiElement rotated 9#usize
  let lane10 ← chiElement rotated 10#usize
  let lane11 ← chiElement rotated 11#usize
  let lane12 ← chiElement rotated 12#usize
  let lane13 ← chiElement rotated 13#usize
  let lane14 ← chiElement rotated 14#usize
  let lane15 ← chiElement rotated 15#usize
  let lane16 ← chiElement rotated 16#usize
  let lane17 ← chiElement rotated 17#usize
  let lane18 ← chiElement rotated 18#usize
  let lane19 ← chiElement rotated 19#usize
  let lane20 ← chiElement rotated 20#usize
  let lane21 ← chiElement rotated 21#usize
  let lane22 ← chiElement rotated 22#usize
  let lane23 ← chiElement rotated 23#usize
  let lane24 ← chiElement rotated 24#usize
  ok (Aeneas.Std.Array.make 25#usize [
    lane0, lane1, lane2, lane3, lane4,
    lane5, lane6, lane7, lane8, lane9,
    lane10, lane11, lane12, lane13, lane14,
    lane15, lane16, lane17, lane18, lane19,
    lane20, lane21, lane22, lane23, lane24])

set_option maxRecDepth 65536 in
theorem source_chi_eq_elements (rotated : State) :
    lean_sphincs.hash.batch.chi rotated = chiElements rotated := by
  conv_rhs => simp only [chiElements, chiElement, Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok]
  rfl

/-- The source helper implements the unchanged lane-wise chi model. -/
@[step] theorem chi_array_spec (rotated : State) :
    lean_sphincs.hash.batch.chi rotated ⦃ out =>
      out = tabulate 25#usize (chi rotated) ⦄ := by
  rw [source_chi_eq_elements]
  unfold chiElements
  step*
  rw [← literal25_tabulate (chi rotated)]
  simp_all

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
