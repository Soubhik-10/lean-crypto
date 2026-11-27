module
public import RustCrypto.Signing.Full.SelectPath
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def layerSuccess (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer)
    (index : Nat) (message : EthLib.Cryptography.Sphincs.Digest) (written : List UInt8)
    (choice : UInt32 × EthLib.Cryptography.Sphincs.Codeword) :
    (Address × U64 × Aeneas.Std.Array U8 7740#usize × Node × Usize × Usize) → Prop
  | (address,sourceIndex,serialized,node,sourceOffset,stage) =>
    let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
    TreePrimitives.frame address seed layer key.tree ∧ sourceIndex.val = key.tree ∧
    (nativeBytes serialized.val).take (offset layer+1028+16*layer.height) =
      written ++ wotsBytes seed secret key choice ++ pathBytes seed secret key ∧
    nativeNode node = nextMessage seed secret key message ∧
    sourceOffset.val = offset layer+1028+16*layer.height ∧ stage.val = layer.toNat+1

@[step] theorem layer_success_spec (secret : Aeneas.Std.Array U8 32#usize) (limit : U64) (cache : lean_sphincs.tree.TopTree)
    (address : Address) (sourceIndex : U64) (serialized : Aeneas.Std.Array U8 7740#usize)
    (node seed : Node) (sourceOffset stage : Usize) (layer oldLayer : EthLib.Cryptography.Sphincs.Layer)
    (oldTree index : Nat) (written : List UInt8) (choice : UInt32 × EthLib.Cryptography.Sphincs.Codeword)
    (hstage : stage.val = layer.toNat) (hoffset : sourceOffset.val = offset layer)
    (hindex : sourceIndex.val = index/2^layer.below) (hbound : index < 67108864)
    (hframe : TreePrimitives.frame address seed oldLayer oldTree)
    (hvalid : TopCache.validThrough cache.nodes seed secret 10)
    (hprefix : (nativeBytes serialized.val).take (offset layer) = written)
    (hchoice : EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) (nativeNode node) 0 limit.val = some choice) :
    lean_sphincs.signing.sign_with_limit_loop.body secret limit cache address sourceIndex serialized node sourceOffset stage ⦃ out =>
      match out with
      | .cont state => layerSuccess seed secret layer index (nativeNode node) written choice state
      | .done _ => False ⦄ := by
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
  have hwotsBytes : nativeBytes nextOutput.val = wotsBytes seed secret key choice := by
    have hd : (nativeBytes wotsOutput.val).drop 1028 = [] := List.drop_eq_nil_iff.mpr (by rw [native_bytes_length,hwotsSizeNat])
    simpa only [hd,List.append_nil] using hresult.2.1
  rw [hresult.1]
  simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have hfull : (do
    let (finalAddress,finalNode,layerOutput,path) ← selectPath secret cache nextAddress node (restoreWots nextOutput) stage
      (stepWord layer.height) (stepWord key.leaf)
    let (pathOutput,restorePath) ← core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut { start := 1028#usize } layerOutput
    let writtenPath ← lean_sphincs.signature.write_nodes pathOutput path
    let nextStage ← stage + 1#usize
    ok (show ControlFlow (Address × U64 × Aeneas.Std.Array U8 7740#usize × Node × Usize × Usize)
      (core.result.Result (Aeneas.Std.Array U8 7740#usize) lean_sphincs.signing.SignError) from
      .cont (finalAddress,nextIndex,restore (restorePath writtenPath),finalNode,endOffset,nextStage))) ⦃ out =>
      match out with
      | .cont state => layerSuccess seed secret layer index (nativeNode node) written choice state
      | .done _ => False ⦄ := by
    step with select_path_spec secret cache nextAddress node seed (restoreWots nextOutput) stage layer index hbound hstage hvalid hresult.2.2
      as ⟨finalAddress,finalNode,layerOutput,path,hfinalFrame,hfinalMessage,hlayerOutput,hpath⟩
    have hLayerSize : layerOutput.val.length = 1028+16*layer.height := by
      rw [hlayerOutput,hrestoreWots,List.length_setSlice!]
      exact houtputSize
    step as ⟨pathOutput,restorePath,hpathOutput,hpathOutputLen,hrestorePath⟩
    have hpSize : pathOutput.val.length = 16*layer.height := by
      dsimp only [Slice.length] at hpathOutputLen
      omega
    step with write_path_spec path pathOutput seed secret key hpSize hheightBound hpath as ⟨writtenPath,hwrittenPath⟩
    step as ⟨nextStage,hnextStage⟩
    simp only [layerSuccess]
    refine ⟨hfinalFrame,htreeVal,?_,hfinalMessage,?_,?_⟩
    · have hwb := wots_bytes_length seed secret key choice
      have hpb : (pathBytes seed secret key).length = 16*layer.height := path_bytes_length seed secret key
      have hlayerNative : nativeBytes (restorePath writtenPath).val = wotsBytes seed secret key choice ++ pathBytes seed secret key := by
        rw [hrestorePath,native_bytes_set,hwrittenPath,hlayerOutput,hrestoreWots,native_bytes_set,hwotsBytes]
        have hs : (nativeBytes output.val).length = (wotsBytes seed secret key choice).length+(pathBytes seed secret key).length := by
          rw [native_bytes_length,houtputSize,hwb,hpb]
        simpa only [hwb] using overwrite_pair (nativeBytes output.val) (wotsBytes seed secret key choice) (pathBytes seed secret key) hs
      rw [hrestore,native_bytes_set,hlayerNative]
      have hroom : sourceOffset.val+(wotsBytes seed secret key choice ++ pathBytes seed secret key).length ≤ (nativeBytes serialized.val).length := by
        rw [List.length_append,hwb,hpb,native_bytes_length]
        have hs : serialized.val.length = 7740 := serialized.property
        omega
      have hp := overwrite_prefix (nativeBytes serialized.val) (wotsBytes seed secret key choice ++ pathBytes seed secret key) sourceOffset.val hroom
      rw [List.length_append,hwb,hpb,hoffset] at hp
      simpa only [hoffset,Nat.add_assoc,hprefix,List.append_assoc] using hp
    · omega
    · scalar_tac
  convert hfull using 1 <;> simp only [selectPath,lift,bind_ok,Aeneas.Std.bind_assoc,key,Node,lean_sphincs.alloy_primitives.bits.fixed.FixedBytes]
  congr 8

end RustCrypto.FullSign
