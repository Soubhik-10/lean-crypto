module

public import EthLib.Cryptography.Hash.Keccak

/-!
Lane-major model of the fused theta/rho/pi/chi/iota loop in hash/batch.rs.
Vector words have componentwise UInt64 semantics. These are model equivalences,
not refinement proofs for Rust, wide, or CPU instructions.
-/
@[expose] public section

namespace Batching.KeccakModel
open EthLib.Cryptography.Hash

abbrev Word (width : Nat) := Fin width → UInt64
abbrev State (width : Nat) := Fin 25 → Word width

def wordAt {width : Nat} (s : State width) (i : Nat) : Word width :=
  s ⟨i % 25, Nat.mod_lt _ (by decide)⟩

def project {width : Nat} (s : State width) (j : Fin width) : Keccak.State :=
  ⟨s 0 j, s 1 j, s 2 j, s 3 j, s 4 j, s 5 j, s 6 j, s 7 j, s 8 j,
   s 9 j, s 10 j, s 11 j, s 12 j, s 13 j, s 14 j, s 15 j, s 16 j,
   s 17 j, s 18 j, s 19 j, s 20 j, s 21 j, s 22 j, s 23 j, s 24 j⟩

/-- The explicit destination rows used by the Rust fused rho/pi mapping. -/
def source : Vector Nat 25 := #v[
  0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20,
  4, 5, 11, 17, 23, 2, 8, 14, 15, 21]

/-- A fused round, operating on lane-major independent message components. -/
def round {width : Nat} (ir : Fin 24) (s : State width) : State width :=
  let parity (x : Nat) (j : Fin width) :=
    wordAt s x j ^^^ wordAt s (x + 5) j ^^^ wordAt s (x + 10) j ^^^
      wordAt s (x + 15) j ^^^ wordAt s (x + 20) j
  let theta (x : Nat) (j : Fin width) :=
    parity ((x + 4) % 5) j ^^^ Keccak.rotl (parity ((x + 1) % 5) j) 1
  let rotated (i : Fin 25) (j : Fin width) :=
    let input := source[i]
    Keccak.rotl (wordAt s input j ^^^ theta (input % 5) j)
      Keccak.RHO[(⟨input % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25)]
  fun i j =>
    let row := i.val / 5 * 5
    let x := i.val % 5
    let value := rotated i j ^^^
      (~~~rotated ⟨(row + (x + 1) % 5) % 25, Nat.mod_lt _ (by decide)⟩ j &&&
        rotated ⟨(row + (x + 2) % 5) % 25, Nat.mod_lt _ (by decide)⟩ j)
    if i.val = 0 then value ^^^ Keccak.RC[ir] else value

/-- Every message component of the fused round equals EthLib's round. -/
theorem project_round {width : Nat} (ir : Fin 24) (s : State width) (j : Fin width) :
    project (round ir s) j = Keccak.round ir (project s j) := by
  rfl

def rounds {width : Nat} (schedule : List (Fin 24)) (s : State width) : State width :=
  schedule.foldl (fun state ir => round ir state) s

/-- Projection commutes with any round schedule, for arbitrary input states. -/
theorem project_rounds {width : Nat} (schedule : List (Fin 24))
    (s : State width) (j : Fin width) :
    project (rounds schedule s) j =
      schedule.foldl (fun state ir => Keccak.round ir state) (project s j) := by
  induction schedule generalizing s with
  | nil => rfl
  | cons ir schedule ih =>
    change project (rounds schedule (round ir s)) j = _
    rw [ih, project_round]
    rfl

def indices : List (Fin 24) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
   12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

def permute {width : Nat} (s : State width) : State width := rounds indices s

/-- Connect the ordinary round loop to EthLib's eight-round unrolling. -/
theorem scalar_rounds (s : Keccak.State) :
    indices.foldl (fun state ir => Keccak.round ir state) s = Keccak.keccakF s := by
  unfold Keccak.keccakF
  rw [Keccak.keccakF.roundsFrom]
  rw [dite_eq_left (by decide : 0 + 8 ≤ Keccak.ROUNDS)]
  rw [Keccak.keccakF.roundsFrom]
  rw [dite_eq_left (by decide : 8 + 8 ≤ Keccak.ROUNDS)]
  rw [Keccak.keccakF.roundsFrom]
  rw [dite_eq_left (by decide : 16 + 8 ≤ Keccak.ROUNDS)]
  rw [Keccak.keccakF.roundsFrom]
  rw [dite_eq_right (by decide : ¬24 + 8 ≤ Keccak.ROUNDS)]
  rw [dite_eq_right (by decide : ¬24 < Keccak.ROUNDS)]
  rfl

/-- The full lane-major permutation equals EthLib independently in every lane. -/
theorem project_permute {width : Nat} (s : State width) (j : Fin width) :
    project (permute s) j = Keccak.keccakF (project s j) := by
  rw [permute, project_rounds, scalar_rounds]

/-- Production SSE2 width. -/
theorem project_permute_sse2 (s : State 2) (j : Fin 2) :
    project (permute s) j = Keccak.keccakF (project s j) := project_permute s j

/-- Production AVX2 width. -/
theorem project_permute_avx2 (s : State 4) (j : Fin 4) :
    project (permute s) j = Keccak.keccakF (project s j) := project_permute s j

end Batching.KeccakModel
