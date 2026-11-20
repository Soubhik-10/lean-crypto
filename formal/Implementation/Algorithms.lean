import Statement.LeanSphincs
import Mathlib.Tactic.FinCases

/-! Rust-shaped Lean descriptions: functional equalities only, not proofs about compiled
Rust or security transfers. Reordered computation uses a fixed stateless permutation. -/
namespace Implementation
open HashSig HashSig.OverPermutation Sphincs

/-- Successive index divisions used by the 8/8/10-bit verifier loop. -/
def indexBefore (index : Nat) : Layer → Nat
  | ⟨0, _⟩ => index
  | ⟨1, _⟩ => index / 256
  | ⟨2, _⟩ => index / 256 / 256
  | ⟨_ + 3, h⟩ => absurd h (by unfold layerCount at h; omega)

theorem indexBefore_eq (index : Index) (layer : Layer) :
    indexBefore index.val layer = index.val / 2 ^ bitsBelowLayer layer := by
  fin_cases layer <;> simp [indexBefore, bitsBelowLayer, Nat.div_div_eq_div_mul]

/-- Loop indices equal the statement's indices for every input and layer. -/
theorem layer_indices (index : Index) (layer : Layer) :
    indexBefore index.val layer % 2 ^ layerHeight layer = (leafOfIndex layer index).val ∧
    indexBefore index.val layer / 2 ^ layerHeight layer = (treeOfIndex layer index).val := by
  rw [indexBefore_eq]
  constructor
  · rfl
  · simp [treeOfIndex, Nat.div_div_eq_div_mul, Nat.pow_add]

/-- One step-major pass. Independent chains retain their original output indices. -/
def round {n : Nat} (hash : Fin n → Nat → Digest → Digest)
    (digits : Fin n → WinternitzDigit) (step : Nat) (values : Fin n → Digest) : Fin n → Digest :=
  fun chain => if (digits chain).val ≤ step then hash chain step (values chain) else values chain

def scheduledEnds {n : Nat} (hash : Fin n → Nat → Digest → Digest)
    (digits : Fin n → WinternitzDigit) (values : Fin n → Digest) : Fin n → Digest :=
  round hash digits 2 (round hash digits 1 (round hash digits 0 values))

/-- Mathematical step-major scheduling equals chain-major recovery for every digit/value.
This proves neither SIMD primitive semantics nor Rust buffering, scatter or scalar-tail code. -/
theorem scheduledEnds_eq_walkChain {n : Nat} (hash : Fin n → Nat → Digest → Digest)
    (digits : Fin n → WinternitzDigit) (values : Fin n → Digest) (chain : Fin n) :
    scheduledEnds hash digits values chain =
    walkChain (m := Id) (fun step : Fin 3 => hash chain step.val)
      (digits chain).val (3 - (digits chain).val) (values chain) := by
  unfold scheduledEnds round
  generalize digits chain = digit
  fin_cases digit <;> simp [walkChain] <;> rfl

/-- Instantiation with the pinned statement's hash under a fixed stateless permutation. -/
theorem scheduledEnds_eq_recoverChain
    (π : LeanVM.Semantics.KeccakState → Id LeanVM.Semantics.KeccakState)
    (seed : PublicParameter) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (digits : Encoding) (values : ChainIndex → Digest) (chain : ChainIndex) :
    scheduledEnds (fun i step value => Verification.tweakableHash (m := Id) π seed
      (.chain layer tree leaf i ⟨step % 3, Nat.mod_lt _ (by decide)⟩)
      (littleEndianBytes 16 value)) digits values chain =
    Verification.recoverChain (m := Id) π seed layer tree leaf chain (digits chain) (values chain) := by
  rw [scheduledEnds_eq_walkChain]
  unfold Verification.recoverChain Verification.chainWalk
  apply congrArg (fun f : Fin 3 → Digest → Id Digest =>
    walkChain f (digits chain).val (3 - (digits chain).val) (values chain))
  funext step value
  have h : (⟨step.val % 3, Nat.mod_lt _ (by decide)⟩ : ChainStep) = step :=
    Fin.ext (Nat.mod_eq_of_lt step.isLt)
  rw [h]

/-- Least-counter search, retaining bounded exhaustion as an ordinary result. -/
def search {α : Type} (encode : Nat → Option α) : Nat → Nat → Option (Nat × α)
  | 0, _ => none
  | attempts + 1, start =>
    match encode start with
    | some value => some (start, value)
    | none => search encode attempts (start + 1)

theorem search_none_iff {α : Type} (encode : Nat → Option α) (attempts start : Nat) :
    search encode attempts start = none ↔
      ∀ c, start ≤ c → c < start + attempts → encode c = none := by
  induction attempts generalizing start with
  | zero =>
    simp only [search, Nat.add_zero]
    constructor
    · intro _ c hlo hhi; omega
    · intro _; trivial
  | succ attempts ih =>
    simp only [search]
    cases h : encode start with
    | none =>
      rw [ih]
      constructor
      · intro hs c hlo hhi
        by_cases hc : c = start
        · simpa [hc] using h
        · exact hs c (by omega) (by omega)
      · intro hs c hlo hhi
        exact hs c (by omega) (by omega)
    | some value =>
      constructor
      · simp
      · intro hs
        have := hs start le_rfl (by omega)
        simp [h] at this

theorem search_some_spec {α : Type} (encode : Nat → Option α) (attempts start c : Nat)
    (value : α) (h : search encode attempts start = some (c, value)) :
    start ≤ c ∧ c < start + attempts ∧ encode c = some value ∧
      ∀ before, start ≤ before → before < c → encode before = none := by
  induction attempts generalizing start with
  | zero => simp [search] at h
  | succ attempts ih =>
    simp only [search] at h
    cases he : encode start with
    | some found =>
      simp [he] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨le_rfl, by omega, he, by intros; omega⟩
    | none =>
      simp only [he] at h
      obtain ⟨hlo, hhi, hv, hleast⟩ := ih (start + 1) h
      refine ⟨by omega, by omega, hv, ?_⟩
      intro before hb hc
      by_cases heq : before = start
      · simpa [heq] using he
      · exact hleast before (by omega) hc

/-- At the actual production limit a successful counter cannot wrap; failure is possible. -/
theorem search_counter_no_wrap {α : Type} (encode : Nat → Option α) (c : Nat) (value : α)
    (h : search encode encodingAttemptLimit 0 = some (c, value)) :
    c < 2 ^ 32 ∧ (BitVec.ofNat counterBits c).toNat = c := by
  have hc := (search_some_spec encode encodingAttemptLimit 0 c value h).2.1
  refine ⟨hc, ?_⟩
  change c % 2 ^ 32 = c
  exact Nat.mod_eq_of_lt hc

open KeyGenerationAndSigning Verification in
/-- The bounded search plus chain opening is the statement's complete WOTS signer, including
failure. This is a functional equality, not an oracle-cost or security-game equivalence. -/
theorem search_eq_otsSignFrom
    (π : LeanVM.Semantics.KeccakState → Id LeanVM.Semantics.KeccakState)
    (key : KeyGenerationAndSigning.ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (attempts start : Nat) :
    (search (fun c => encode (m := Id) π key.publicSeed layer tree leaf message
      (BitVec.ofNat counterBits c)) attempts start).map (fun (c, digits) =>
        let secrets := otsSecrets (m := Id) π key layer tree leaf
        (BitVec.ofNat counterBits c, sequenceFin (m := Id) fun i =>
          chainWalk (m := Id) π key.publicSeed layer tree leaf i 0 (digits i).val (secrets i))) =
    otsSignFrom (m := Id) π key layer tree leaf message attempts start := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
    simp only [search, otsSignFrom]
    cases h : encode (m := Id) π key.publicSeed layer tree leaf message (BitVec.ofNat counterBits start) with
    | none => exact ih (start + 1)
    | some digits => rfl

end Implementation