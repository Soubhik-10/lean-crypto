module
public import RustCrypto.Hash.Keccak.Permutation
public import Mathlib.Tactic.IntervalCases
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Permutation
set_option maxHeartbeats 4000000

def toUInt (word : U64) : UInt64 := UInt64.ofBitVec word.bv

@[simp] theorem toUInt_xor (a b : U64) : toUInt (a ^^^ b) = toUInt a ^^^ toUInt b := by rfl
@[simp] theorem toUInt_and (a b : U64) : toUInt (a &&& b) = toUInt a &&& toUInt b := by rfl
@[simp] theorem toUInt_not (a : U64) : toUInt (~~~a) = ~~~toUInt a := by rfl

@[simp] theorem toUInt_rotate (n : Nat) (hn : n < 64) (word : Word) (lane) :
    toUInt (rotateWord n word lane) =
      EthLib.Cryptography.Hash.Keccak.rotl (toUInt (word lane)) (UInt64.ofNat n) := by
  interval_cases n <;> first
  | rfl
  | apply UInt64.toBitVec_inj.1
    simp only [toUInt, rotateWord, EthLib.Cryptography.Hash.Keccak.rotl,
      BitVec.rotateLeft_def, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight]
    simp [BitVec.ushiftRight_eq_zero]

end RustCrypto.Permutation
