module
public import RustCrypto.Fors.Scalar.Full
public import RustCrypto.Tree.ClimbShort
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsScalar
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem body_short_spec (address : Address) (reader : Slice U8) (roots : List U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) (index : Usize)
    (hindex : index.val < 24) (hreader : reader.val.length < 176)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop.body digest address reader roots index ⦃ out =>
      match out with
      | .cont _ => False
      | .done (status,nextAddress,remaining,nextRoots) =>
          status = none ∧ keyFrame nextAddress seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ∧
          remaining.val = reader.val.drop (16*(reader.val.length/16)) ∧ nextRoots = roots ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx
  unfold lean_sphincs.fors.recover_trees_loop.body
  have hrun : index < lean_sphincs.params.FORS_TREES := by
    simp only [lean_sphincs.params.FORS_TREES]
    scalar_tac
  simp only [ite_eq_left hrun]
  step with RustCrypto.ForsDigest.leaf_position_spec digest index hindex as ⟨position,hposition⟩
  rcases hframe with ⟨old2,old3,hhead⟩
  step with ForsPrimitives.position_frame_spec address seed key.layer key.tree (addressTag .forsTree) (stepWord key.leaf)
    old2 old3 0#u32 position hhead as ⟨positionedAddress,hpositioned⟩
  have hpositionedFrame : keyFrame positionedAddress seed key .forsTree := ⟨0#u32,position,hpositioned⟩
  by_cases hsmall : reader.val.length < 16
  · rw [RustParser.take_failure 16#usize reader (by scalar_tac)]
    simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
    refine ⟨True.intro,hpositionedFrame,?_,True.intro⟩
    have hzero : reader.val.length/16 = 0 := by omega
    simp only [hzero,Nat.mul_zero,List.drop_zero]
  · have hread : (16#usize).val ≤ reader.val.length := by scalar_tac
    rw [RustParser.take_success 16#usize reader hread]
    simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    step with RustCrypto.hash_node_spec positionedAddress (RustParser.readPrefix 16#usize reader hread)
      as ⟨node,hashedAddress,hnode,hhashed⟩
    have hhashedFrame : keyFrame hashedAddress seed key .forsTree := by
      refine ⟨0#u32,position,?_⟩
      calc
        _ = positionedAddress.val.take 48 := by
          rw [hhashed]
          simp [List.setSlice!,List.take_of_length_le]
        _ = _ := hpositioned
    simp only [lean_sphincs.params.FORS_HEIGHT]
    have h16 : (16#usize).val = 16 := rfl
    have hshort : (RustParser.readSuffix 16#usize reader).val.length < 16*(10#u32).val := by
      change (RustParser.readSuffix 16#usize reader).val.length < 160
      simp only [RustParser.readSuffix,Slice.from_val,h16,List.length_drop]
      omega
    step with climb_key_short_spec hashedAddress (RustParser.readSuffix 16#usize reader) position 10#u32 node seed key .forsTree
      (by decide) hshort hhashedFrame as ⟨status,nextAddress,remaining,hstatus,hremaining,hnextFrame⟩
    rw [hstatus]
    simp only [bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
    refine ⟨True.intro,hnextFrame,?_,True.intro⟩
    rw [hremaining]
    simp only [RustParser.readSuffix,Slice.from_val,h16,List.length_drop,List.drop_drop]
    congr 1
    omega

end RustCrypto.ForsScalar
