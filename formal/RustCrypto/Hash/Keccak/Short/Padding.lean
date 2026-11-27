module
public import RustCrypto.Hash.Keccak.Short.Load
public import RustCrypto.Hash.Keccak.Loop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ShortHash
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
abbrev State := RustCrypto.Permutation.State

def highWord : U64 := ⟨1#64 <<< 63⟩

def padded (position : Usize) (state : State) : State :=
  let first := state.set position (fun _ => 1#u64)
  first.set 16#usize (fun lane => first[16]! lane ||| highWord)

@[simp] theorem word_or (a b : U64) : ByteBridge.word (a ||| b) = ByteBridge.word a ||| ByteBridge.word b := by rfl
@[simp] theorem toUInt_or (a b : U64) : Permutation.toUInt (a ||| b) = Permutation.toUInt a ||| Permutation.toUInt b := by rfl

theorem padding_64 (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize)
    (state : State) (hstate : ∀ i < 25, ∀ lane : Fin 2,
      ByteBridge.word (state[i]! lane) = if i < 8 then
        EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs[lane.val]!).val) (8*i) else 0)
    (lane : Fin 2) :
    Batching.KeccakModel.project (Permutation.asModel (padded 8#usize state)) lane =
      EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
        EthLib.Cryptography.Hash.Keccak.keccakF 136 64
        (EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane.val]!).val)) := by
  have hinput : lane.val < inputs.val.length := by
    have hi := lane.isLt
    scalar_tac
  have hword (i : Nat) (hi : i < 25) :
      UInt64.ofBitVec ((state.val[i]'(by simpa using hi)) lane).bv =
        if i < 8 then EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs.val[lane.val]'hinput).val) (8*i) else 0 := by
    simpa only [ByteBridge.word, Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state.val i (by simpa using hi),
      getElem!_pos inputs.val lane.val hinput] using hstate i hi lane
  have htail (i : Nat) (hi : 64 ≤ i) :
      EthLib.Cryptography.Hash.Keccak.Internal.laneAt
        (RustCrypto.bytes (inputs.val[lane.val]'hinput).val) i = 0 := by
    apply ByteBridge.laneAt_beyond
    have hlen := (inputs.val[lane.val]'hinput).property
    simpa using hi
  simp (disch := scalar_tac) [padded, Permutation.asModel, Permutation.wordAt,
    Batching.KeccakModel.project, hword, htail,
    EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation,
    EthLib.Cryptography.Hash.Keccak.Internal.absorbBlocks,
    EthLib.Cryptography.Hash.Keccak.Internal.absorbBlock,
    EthLib.Cryptography.Hash.Keccak.Internal.blockLane,
    EthLib.Cryptography.Hash.Keccak.Internal.xorBlockByte,
    EthLib.Cryptography.Hash.Keccak.State.xorLane,
    EthLib.Cryptography.Hash.Keccak.State.zero, highWord, Permutation.toUInt]

theorem padding_80 (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize)
    (state : State) (hstate : ∀ i < 25, ∀ lane : Fin 2,
      ByteBridge.word (state[i]! lane) = if i < 10 then
        EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs[lane.val]!).val) (8*i) else 0)
    (lane : Fin 2) :
    Batching.KeccakModel.project (Permutation.asModel (padded 10#usize state)) lane =
      EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
        EthLib.Cryptography.Hash.Keccak.keccakF 136 80
        (EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane.val]!).val)) := by
  have hinput : lane.val < inputs.val.length := by
    have hi := lane.isLt
    scalar_tac
  have hword (i : Nat) (hi : i < 25) :
      UInt64.ofBitVec ((state.val[i]'(by simpa using hi)) lane).bv =
        if i < 10 then EthLib.Cryptography.Hash.Keccak.Internal.laneAt
          (RustCrypto.bytes (inputs.val[lane.val]'hinput).val) (8*i) else 0 := by
    simpa only [ByteBridge.word, Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state.val i (by simpa using hi),
      getElem!_pos inputs.val lane.val hinput] using hstate i hi lane
  have htail (i : Nat) (hi : 80 ≤ i) :
      EthLib.Cryptography.Hash.Keccak.Internal.laneAt
        (RustCrypto.bytes (inputs.val[lane.val]'hinput).val) i = 0 := by
    apply ByteBridge.laneAt_beyond
    have hlen := (inputs.val[lane.val]'hinput).property
    simpa using hi
  simp (disch := scalar_tac) [padded, Permutation.asModel, Permutation.wordAt,
    Batching.KeccakModel.project, hword, htail,
    EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation,
    EthLib.Cryptography.Hash.Keccak.Internal.absorbBlocks,
    EthLib.Cryptography.Hash.Keccak.Internal.absorbBlock,
    EthLib.Cryptography.Hash.Keccak.Internal.blockLane,
    EthLib.Cryptography.Hash.Keccak.Internal.xorBlockByte,
    EthLib.Cryptography.Hash.Keccak.State.xorLane,
    EthLib.Cryptography.Hash.Keccak.State.zero, highWord, Permutation.toUInt]

end RustCrypto.ShortHash
