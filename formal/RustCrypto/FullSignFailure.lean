module
public import RustCrypto.FullSignBuffer
public import RustCrypto.LayerIndex
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

@[step] theorem layer_failure_spec (secret : Aeneas.Std.Array U8 32#usize) (limit : U64) (cache : lean_sphincs.tree.TopTree)
    (address : Address) (sourceIndex : U64) (serialized : Aeneas.Std.Array U8 7740#usize)
    (node seed : Node) (sourceOffset stage : Usize) (layer oldLayer : EthLib.Cryptography.Sphincs.Layer)
    (oldTree index : Nat) (hstage : stage.val = layer.toNat) (hoffset : sourceOffset.val = offset layer)
    (hindex : sourceIndex.val = index/2^layer.below) (hframe : TreePrimitives.frame address seed oldLayer oldTree)
    (hchoice : EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) (nativeNode node) 0 limit.val = none) :
    lean_sphincs.signing.sign_with_limit_loop.body secret limit cache address sourceIndex serialized node sourceOffset stage ⦃ out =>
      match out with
      | .cont _ => False
      | .done result => nativeResult result = .error layer.toNat ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
  have hstageBound : stage.val < 3 := by rw [hstage]; cases layer <;> decide
  have hcapacity := layer_offset_bound layer
  have hheightBound := layer_height_bound layer
  have hrun : stage < Slice.len (Aeneas.Std.Array.to_slice lean_sphincs.params.LAYER_HEIGHTS) := by
    simp [Slice.len,Aeneas.Std.Array.to_slice,Slice.from_val,RustIndex.layer_heights_eq]
    scalar_tac
  unfold lean_sphincs.signing.sign_with_limit_loop.body
  simp only [lift,bind_ok]
  simp only [ite_eq_left hrun]
  step as ⟨height,hheight⟩
  have hh : height = stepWord layer.height := by
    have he : height = lean_sphincs.params.LAYER_HEIGHTS.val[stage.val]! := by
      rw [getElem!_pos _ stage.val (by scalar_tac)]
      exact hheight
    rw [he,hstage,height_index]
  rw [hh]
  step with LayerInput.take_layer_typed_spec sourceIndex layer index hindex as ⟨leaf,nextIndex,hleaf,htree,htreeVal⟩
  rw [hleaf]
  have hcast : UScalar.cast .U32 stage = stepWord layer.toNat := by
    apply UScalar.eq_of_val_eq
    rw [layer_word_val]
    scalar_tac
  rw [hcast]
  have hs := ContextFrame.set_tree_frame_spec address seed oldLayer layer oldTree key.tree hframe
  rw [←htree] at hs
  step with hs as ⟨layerAddress,hlayerFrame⟩
  simp only [lean_sphincs.params.NODE_BYTES]
  have hcastHeight : (UScalar.cast .Usize (stepWord layer.height)).val = layer.height := by
    rw [UScalar.cast_val_eq,LayerInput.height_word_val]
    have hm : layer.height % 2^System.Platform.numBits = layer.height := Nat.mod_eq_of_lt (by have hp := System.Platform.numBits_eq; cases hp <;> scalar_tac)
    exact hm
  step as ⟨pathSize,hpathSize⟩
  have hpathVal : pathSize.val = 16*layer.height := by scalar_tac
  step with wots_size_spec as ⟨wotsSize,hwotsSize⟩
  rw [hwotsSize]
  step as ⟨layerSize,hlayerSize⟩
  have hsizeVal : layerSize.val = 1028+16*layer.height := by scalar_tac
  step as ⟨endOffset,hendOffset⟩
  have hendVal : endOffset.val = sourceOffset.val+1028+16*layer.height := by scalar_tac
  simp only [alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndexMut.index_mut,
    lean_sphincs.core.ops.index.IndexMutArray,Aeneas.Std.core.ops.index.IndexMutArray]
  step as ⟨output,restore,houtput,houtputLen,hrestore⟩
  have houtputSize : output.val.length = 1028+16*layer.height := by
    dsimp only [Slice.length] at houtputLen
    omega
  step as ⟨wotsOutput,restoreWots,hwotsOutput,hwotsOutputLen,hrestoreWots⟩
  have hwotsSizeNat : wotsOutput.val.length = 1028 := by
    dsimp only [Slice.length] at hwotsOutputLen
    exact hwotsOutputLen
  step with wots_sign_spec layerAddress seed secret key node wotsOutput limit hlayerFrame (by omega)
    as ⟨status,nextAddress,nextOutput,hresult⟩
  simp only [wotsResult,hchoice] at hresult
  rw [hresult.1]
  simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from,nativeResult]
  step*

end RustCrypto.FullSign
