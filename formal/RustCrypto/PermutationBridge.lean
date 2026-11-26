module
public import RustCrypto.WordBridge
public import Mathlib.Tactic.FinCases
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Permutation
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def asModel (state : State) : Batching.KeccakModel.State width :=
  fun i lane => toUInt (wordAt state i.val lane)

@[simp] theorem toUInt_constant (ir : Fin 24) :
    toUInt (RustCrypto.RoundConstants.constantArray[ir.val]!) =
      EthLib.Cryptography.Hash.Keccak.RC[ir] := by
  simp only [RustCrypto.RoundConstants.constantArray, Aeneas.Std.Array.getElem!_Nat_eq,
    Aeneas.Std.Array.from_val]
  rw [getElem!_pos _ ir.val (by rw [List.length_map, Vector.length_toList]; exact ir.isLt)]
  simp only [List.getElem_map, Vector.getElem_toList, toUInt]
  rfl

/-- The pure result of the source fused round equals EthLib's lane-major round. -/
theorem asModel_round (ir : Fin 24) (state : State) :
    asModel (roundModel (RustCrypto.RoundConstants.constantArray[ir.val]!) state) =
      Batching.KeccakModel.round ir (asModel state) := by
  have hconstant := toUInt_constant ir
  rw [Aeneas.Std.Array.getElem!_Nat_eq,
    getElem!_pos RustCrypto.RoundConstants.constantArray.val ir.val (by simp)] at hconstant
  funext i lane
  fin_cases i <;>
    simp [asModel, roundModel, rhoPi, chi, theta, parity, wordAt, tabulate,
      Aeneas.Std.Array.getElem!_Nat_eq, Aeneas.Std.Array.make,
      Aeneas.Std.Array.set, Aeneas.Std.Array.from_val,
      Batching.KeccakModel.round, Batching.KeccakModel.wordAt, Batching.KeccakModel.source,
      EthLib.Cryptography.Hash.Keccak.RHO]
  all_goals first | rfl | (rw [hconstant]; rfl)

end RustCrypto.Permutation
