module
public import RustCrypto.Hash.Keccak.Short.Load
public import RustCrypto.Hash.Keccak.Short.Padding
public import RustCrypto.Hash.Keccak.Short.Store
public import RustCrypto.Serialization.WriteBytes
public import RustCrypto.Common.ByteRelations
public import RustCrypto.Hash.Keccak.Loop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ShortHash
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

@[step] theorem wide_or_assign_spec (a b : wide.u64x2_.u64x2) :
    wide.u64x2_.u64x2.Insts.CoreOpsBitBitOrAssignu64x2.bitor_assign a b ⦃ out =>
      out = fun lane => a lane ||| b lane ⦄ := by
  simp [wide.u64x2_.u64x2.Insts.CoreOpsBitBitOrAssignu64x2.bitor_assign, WP.spec_ok]

@[step] theorem wide_to_array_spec (input : wide.u64x2_.u64x2) :
    wide.u64x2_.u64x2.to_array input ⦃ out =>
      out = Aeneas.Std.Array.from (List.ofFn input) (by simp) ⦄ := by
  simp [wide.u64x2_.u64x2.to_array, WP.spec_ok]


theorem wide_array_get (input : wide.u64x2_.u64x2) (lane : Fin 2) :
    (Aeneas.Std.Array.from (List.ofFn input) (by simp) : Aeneas.Std.Array U64 2#usize)[lane.val]! = input lane := by
  simp only [Aeneas.Std.Array.getElem!_Nat_eq, Aeneas.Std.Array.from_val]
  rw [getElem!_pos (List.ofFn input) lane.val (by simpa only [List.length_ofFn] using lane.isLt)]
  simp only [List.getElem_ofFn]

theorem project_a0 (state : Permutation.State) (lane : Fin 2) :
    (Batching.KeccakModel.project (Permutation.asModel state) lane).a0 =
      ByteBridge.word (state[0]! lane) := by rfl

theorem project_a1 (state : Permutation.State) (lane : Fin 2) :
    (Batching.KeccakModel.project (Permutation.asModel state) lane).a1 =
      ByteBridge.word (state[1]! lane) := by rfl

theorem first16_keccak (message : ByteArray) :
    (EthLib.Cryptography.Hash.Keccak.keccak256 message).toList.take 16 =
      let finalState := EthLib.Cryptography.Hash.Keccak.keccakF
        (EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
          EthLib.Cryptography.Hash.Keccak.keccakF 136 message.size
          (EthLib.Cryptography.Hash.Keccak.Internal.laneAt message))
      EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane finalState.a0 ++
        EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane finalState.a1 := by
  simp [EthLib.Cryptography.Hash.Keccak.keccak256,
    EthLib.Cryptography.Hash.Keccak.Internal.keccak256Read,
    EthLib.Cryptography.Hash.Keccak.Internal.spongeAbsorb,
    EthLib.Cryptography.Hash.Keccak.Internal.squeezeLanes256,
    EthLib.Cryptography.Hash.Keccak.Lanes4.bytes,
    EthLib.Cryptography.Hash.Keccak.Internal.bytesOfLane,
    EthLib.Cryptography.Hash.Keccak.RATE_256, Vector.toList]

theorem hash_64_spec (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize) :
    lean_sphincs.hash.batch.hash inputs ⦃ out => ∀ lane : Fin 2,
      (out[lane.val]!).val.map (fun value => UInt8.ofBitVec value.bv) =
        (EthLib.Cryptography.Hash.Keccak.keccak256 (RustCrypto.bytes (inputs[lane.val]!).val)).toList.take 16 ⦄ := by
  unfold lean_sphincs.hash.batch.hash
  simp only [lean_sphincs.hash.batch.RATE_LANES]
  step*
  have hip : i = 8#usize := by scalar_tac
  have hlast : i1 = 16#usize := by scalar_tac
  have hhigh : i2 = highWord := by
    apply (UScalar.eq_equiv_bv_eq i2 highWord).mpr
    exact i2_post1
  subst i
  subst i1
  subst i2
  have hone : ux = fun _ => 1#u64 := by
    rw [ux_post]
    funext j
    fin_cases j <;> rfl
  have hmask : ux2 = fun _ => highWord := by
    rw [ux2_post]
    funext j
    fin_cases j <;> rfl
  have hread : ux1 = state1[(16#usize).val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state1.val (16#usize).val (by scalar_tac)]
    exact ux1_post
  have hsetup : index_mut_back ux3 = padded 8#usize state := by
    rw [index_mut_back_post, ux3_post, hread, state1_post, hone, hmask]
    unfold padded
    simp only [i1_post]
  have hperm := state3_post lane
  rw [hsetup, padding_64 inputs state (by simpa using state_post) lane] at hperm
  have hlo : ByteBridge.word (low[lane.val]!) =
      (EthLib.Cryptography.Hash.Keccak.keccakF
        (EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
          EthLib.Cryptography.Hash.Keccak.keccakF 136 64
          (EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane.val]!).val)))).a0 := by
    rw [low_post, wide_array_get, ux4_post]
    have hp := congrArg EthLib.Cryptography.Hash.Keccak.State.a0 hperm
    simpa only [project_a0,
      Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state3.val 0 (by scalar_tac)] using hp
  have hhi : ByteBridge.word (high[lane.val]!) =
      (EthLib.Cryptography.Hash.Keccak.keccakF
        (EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
          EthLib.Cryptography.Hash.Keccak.keccakF 136 64
          (EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane.val]!).val)))).a1 := by
    rw [high_post, wide_array_get, ux5_post]
    have hp := congrArg EthLib.Cryptography.Hash.Keccak.State.a1 hperm
    simpa only [project_a1,
      Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state3.val 1 (by scalar_tac)] using hp
  rw [out_post lane.val lane.isLt, List.map_append,
    ByteBridge.encode_eight, ByteBridge.encode_eight, hlo, hhi]
  symm
  simpa using
    first16_keccak (RustCrypto.bytes (inputs[lane.val]!).val)

theorem hash_80_spec (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize) :
    lean_sphincs.hash.batch.hash inputs ⦃ out => ∀ lane : Fin 2,
      (out[lane.val]!).val.map (fun value => UInt8.ofBitVec value.bv) =
        (EthLib.Cryptography.Hash.Keccak.keccak256 (RustCrypto.bytes (inputs[lane.val]!).val)).toList.take 16 ⦄ := by
  unfold lean_sphincs.hash.batch.hash
  simp only [lean_sphincs.hash.batch.RATE_LANES]
  step*
  have hip : i = 10#usize := by scalar_tac
  have hlast : i1 = 16#usize := by scalar_tac
  have hhigh : i2 = highWord := by
    apply (UScalar.eq_equiv_bv_eq i2 highWord).mpr
    exact i2_post1
  subst i
  subst i1
  subst i2
  have hone : ux = fun _ => 1#u64 := by
    rw [ux_post]
    funext j
    fin_cases j <;> rfl
  have hmask : ux2 = fun _ => highWord := by
    rw [ux2_post]
    funext j
    fin_cases j <;> rfl
  have hread : ux1 = state1[(16#usize).val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state1.val (16#usize).val (by scalar_tac)]
    exact ux1_post
  have hsetup : index_mut_back ux3 = padded 10#usize state := by
    rw [index_mut_back_post, ux3_post, hread, state1_post, hone, hmask]
    unfold padded
    simp only [i1_post]
  have hperm := state3_post lane
  rw [hsetup, padding_80 inputs state (by simpa using state_post) lane] at hperm
  have hlo : ByteBridge.word (low[lane.val]!) =
      (EthLib.Cryptography.Hash.Keccak.keccakF
        (EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
          EthLib.Cryptography.Hash.Keccak.keccakF 136 80
          (EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane.val]!).val)))).a0 := by
    rw [low_post, wide_array_get, ux4_post]
    have hp := congrArg EthLib.Cryptography.Hash.Keccak.State.a0 hperm
    simpa only [project_a0,
      Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state3.val 0 (by scalar_tac)] using hp
  have hhi : ByteBridge.word (high[lane.val]!) =
      (EthLib.Cryptography.Hash.Keccak.keccakF
        (EthLib.Cryptography.Hash.Keccak.Internal.stateBeforeLastPermutation
          EthLib.Cryptography.Hash.Keccak.keccakF 136 80
          (EthLib.Cryptography.Hash.Keccak.Internal.laneAt (RustCrypto.bytes (inputs[lane.val]!).val)))).a1 := by
    rw [high_post, wide_array_get, ux5_post]
    have hp := congrArg EthLib.Cryptography.Hash.Keccak.State.a1 hperm
    simpa only [project_a1,
      Aeneas.Std.Array.getElem!_Nat_eq,
      getElem!_pos state3.val 1 (by scalar_tac)] using hp
  rw [out_post lane.val lane.isLt, List.map_append,
    ByteBridge.encode_eight, ByteBridge.encode_eight, hlo, hhi]
  symm
  simpa using
    first16_keccak (RustCrypto.bytes (inputs[lane.val]!).val)

/-- Source batching agrees with the scalar hash boundary in the original source byte type. -/
@[step] theorem hash_64_bytes_spec (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 64#usize) 2#usize) :
    lean_sphincs.hash.batch.hash inputs ⦃ out => ∀ lane : Fin 2,
      (out[lane.val]!).val = (RustCrypto.digest (inputs[lane.val]!).val).val.take 16 ⦄ := by
  apply WP.spec_mono (hash_64_spec inputs)
  intro out hout lane
  apply ByteBridge.native_list_injective
  rw [List.map_take, ByteBridge.digest_native]
  exact hout lane

/-- Source batching agrees with the scalar hash boundary in the original source byte type. -/
@[step] theorem hash_80_bytes_spec (inputs : Aeneas.Std.Array (Aeneas.Std.Array U8 80#usize) 2#usize) :
    lean_sphincs.hash.batch.hash inputs ⦃ out => ∀ lane : Fin 2,
      (out[lane.val]!).val = (RustCrypto.digest (inputs[lane.val]!).val).val.take 16 ⦄ := by
  apply WP.spec_mono (hash_80_spec inputs)
  intro out hout lane
  apply ByteBridge.native_list_injective
  rw [List.map_take, ByteBridge.digest_native]
  exact hout lane

end RustCrypto.ShortHash
