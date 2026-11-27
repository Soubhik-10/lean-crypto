module

public import Batching.Keccak
public import Init.Data.UInt.Bitwise

/-!
Closed constants are evaluated by the kernel. The recurrences below follow the
Rust constant generators; they do not use native decision or external axioms.
-/
@[expose] public section

namespace Batching.Constants
open EthLib.Cryptography.Hash

/-- Seven successive LFSR bits of a Rust round-constant generator. -/
def bits : Nat → Nat → UInt8 → UInt64 → UInt64 × UInt8
  | 0, _, lfsr, constant => (constant, lfsr)
  | remaining + 1, j, lfsr, constant =>
    let constant := constant ||| ((lfsr &&& 1).toUInt64 <<< UInt64.ofNat (2 ^ j - 1))
    let feedback : UInt8 := if lfsr &&& 0x80 != 0 then 0x71 else 0
    bits remaining (j + 1) ((lfsr <<< 1) ^^^ feedback) constant

def rounds : Nat → UInt8 → List UInt64
  | 0, _ => []
  | count + 1, lfsr =>
    let (constant, next) := bits 7 0 lfsr 0
    constant :: rounds count next

/-- The Rust LFSR recurrence produces exactly EthLib's 24 constants. -/
theorem round_constants_eq : rounds 24 1 = Keccak.RC.toList := by decide

/-- Structural version of the Rust coordinate walk, retaining all 25 offsets. -/
def offsetWalk : Nat → Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, _, offsets => offsets
  | remaining + 1, t, x, y, offsets =>
    offsetWalk remaining (t + 1) y ((2 * x + 3 * y) % 5)
      (offsets.set (x + 5 * y) (((t + 1) * (t + 2) / 2) % 64))

def rotationOffsets : List Nat := offsetWalk 24 0 1 0 (List.replicate 25 0)

/-- The generated rotation table equals the pinned EthLib table entry for entry. -/
theorem rotation_offsets_eq : rotationOffsets.map UInt64.ofNat = Keccak.RHO.toList := by decide

/-- The Rust zero-rotation branch avoids a shift by 64. -/
def rustRotate (v : UInt64) (n : Fin 64) : UInt64 :=
  if n.val = 0 then v
  else (v <<< UInt64.ofNat n.val) ||| (v >>> (64 - UInt64.ofNat n.val))

/-- That branch has the same word semantics as EthLib's rotation. -/
theorem rustRotate_eq (v : UInt64) (n : Fin 64) :
    rustRotate v n = Keccak.rotl v (UInt64.ofNat n.val) := by
  by_cases h : n.val = 0
  · simp [rustRotate, h, Keccak.rotl, ← UInt64.toBitVec_inj]
  · simp [rustRotate, h, Keccak.rotl]
end Batching.Constants
