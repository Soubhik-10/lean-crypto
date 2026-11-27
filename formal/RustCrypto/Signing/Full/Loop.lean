module
public import RustCrypto.Signing.Full.Success
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def stageOffset : Nat → Nat | 0 => 4240 | 1 => 5396 | 2 => 6552 | _ => 7740
def stageBelow : Nat → Nat | 0 => 0 | 1 => 8 | 2 => 16 | _ => 26

theorem stage_offset (layer : EthLib.Cryptography.Sphincs.Layer) : stageOffset layer.toNat = offset layer := by cases layer <;> rfl
theorem stage_below (layer : EthLib.Cryptography.Sphincs.Layer) : stageBelow layer.toNat = layer.below := by cases layer <;> rfl
theorem next_stage_offset (layer : EthLib.Cryptography.Sphincs.Layer) : stageOffset (layer.toNat+1) = offset layer+1028+16*layer.height := by cases layer <;> decide
theorem next_stage_index (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree = index/2^(stageBelow (layer.toNat+1)) := by
  cases layer <;> simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,Nat.shiftRight_eq_div_pow,
    EthLib.Cryptography.Sphincs.Layer.below,EthLib.Cryptography.Sphincs.Layer.height,
    EthLib.Cryptography.Sphincs.Layer.toNat,stageBelow,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT,EthLib.Cryptography.Sphincs.Constants.TOP_HEIGHT]

def loopInvariant (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index limit : Nat)
    (expected : Except Nat (List UInt8)) :
    (Address × U64 × Aeneas.Std.Array U8 7740#usize × Node × Usize × Usize) → Prop
  | (address,sourceIndex,serialized,node,sourceOffset,stage) =>
    stage.val ≤ 3 ∧ sourceOffset.val = stageOffset stage.val ∧ sourceIndex.val = index/2^(stageBelow stage.val) ∧
    (∃ layer tree, TreePrimitives.frame address seed layer tree) ∧
    runStages seed secret index limit (stages.drop stage.val) (nativeNode node)
      ((nativeBytes serialized.val).take sourceOffset.val) = expected

@[step] theorem loop_spec (secret : Aeneas.Std.Array U8 32#usize) (limit : U64) (cache : lean_sphincs.tree.TopTree)
    (address : Address) (sourceIndex : U64) (serialized : Aeneas.Std.Array U8 7740#usize)
    (node seed : Node) (index : Nat) (oldLayer : EthLib.Cryptography.Sphincs.Layer) (oldTree : Nat)
    (hindex : sourceIndex.val = index) (hbound : index < 67108864)
    (hframe : TreePrimitives.frame address seed oldLayer oldTree)
    (hvalid : TopCache.validThrough cache.nodes seed secret 10) :
    lean_sphincs.signing.sign_with_limit_loop secret limit address cache sourceIndex serialized node 4240#usize 0#usize ⦃ result =>
      nativeResult result = runStages seed secret index limit.val stages (nativeNode node) ((nativeBytes serialized.val).take 4240) ⦄ := by
  let expected := runStages seed secret index limit.val stages (nativeNode node) ((nativeBytes serialized.val).take 4240)
  unfold lean_sphincs.signing.sign_with_limit_loop
  apply loop.spec_decr_nat
    (fun state : Address × U64 × Aeneas.Std.Array U8 7740#usize × Node × Usize × Usize => 3-state.2.2.2.2.2.val)
    (loopInvariant seed secret index limit.val expected)
  · rintro ⟨currentAddress,currentIndex,currentBytes,currentNode,currentOffset,currentStage⟩
      ⟨hstage,hoffset,hcurrentIndex,⟨currentLayer,currentTree,hcurrentFrame⟩,hmodel⟩
    by_cases hrun : currentStage.val < 3
    · have hex : ∃ layer : EthLib.Cryptography.Sphincs.Layer, currentStage.val = layer.toNat := by
        have hc : currentStage.val = 0 ∨ currentStage.val = 1 ∨ currentStage.val = 2 := by omega
        rcases hc with h | h | h
        · exact ⟨.bottom,h⟩
        · exact ⟨.middle,h⟩
        · exact ⟨.top,h⟩
      obtain ⟨layer,hlayer⟩ := hex
      have ho : currentOffset.val = offset layer := by rw [hoffset,hlayer,stage_offset]
      have hi : currentIndex.val = index/2^layer.below := by rw [hcurrentIndex,hlayer,stage_below]
      cases hc : EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
          (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) (nativeNode currentNode) 0 limit.val with
      | none =>
        apply WP.spec_mono (layer_failure_spec secret limit cache currentAddress currentIndex currentBytes currentNode seed
          currentOffset currentStage layer currentLayer currentTree index hlayer ho hi hcurrentFrame hc)
        intro result hresult
        cases result with
        | cont _ => exact False.elim hresult
        | done result =>
          rw [hlayer,stage_list,runStages,hc] at hmodel
          exact hresult.trans hmodel
      | some choice =>
        apply WP.spec_mono (layer_success_spec secret limit cache currentAddress currentIndex currentBytes currentNode seed
          currentOffset currentStage layer currentLayer currentTree index ((nativeBytes currentBytes.val).take (offset layer))
          choice hlayer ho hi hbound hcurrentFrame hvalid rfl hc)
        intro result hresult
        cases result with
        | done _ => exact False.elim hresult
        | cont state =>
          rcases state with ⟨nextAddress,nextIndex,nextBytes,nextNode,nextOffset,nextStage⟩
          rcases hresult with ⟨hnextFrame,hnextIndex,hnextPrefix,hnextMessage,hnextOffset,hnextStage⟩
          dsimp only
          have hnewStage : nextStage.val = currentStage.val+1 := by omega
          refine ⟨?_,by omega⟩
          refine ⟨by omega,?_,?_,⟨layer,_,hnextFrame⟩,?_⟩
          · rw [hnextOffset,hnextStage,next_stage_offset]
          · rw [hnextIndex,hnextStage,next_stage_index]
          · rw [hlayer,stage_list,runStages,hc,ho] at hmodel
            rw [hnextStage,hnextOffset,hnextMessage,hnextPrefix]
            exact hmodel
    · have hc : currentStage.val = 3 := by omega
      unfold lean_sphincs.signing.sign_with_limit_loop.body
      simp only [lift,bind_ok]
      have hstop : ¬currentStage < Slice.len (Aeneas.Std.Array.to_slice lean_sphincs.params.LAYER_HEIGHTS) := by
        simp [Slice.len,Aeneas.Std.Array.to_slice,Slice.from_val,RustIndex.layer_heights_eq]
        scalar_tac
      simp only [ite_eq_right hstop,WP.spec_ok,nativeResult]
      have ho : currentOffset.val = 7740 := by rw [hoffset,hc]; rfl
      have hm : runStages seed secret index limit.val (stages.drop 3) (nativeNode currentNode)
          ((nativeBytes currentBytes.val).take 7740) = expected := by simpa only [hc,ho] using hmodel
      have hb : (nativeBytes currentBytes.val).length ≤ 7740 := by rw [native_bytes_length]; exact Nat.le_of_eq currentBytes.property
      have hn : stages.drop 3 = [] := rfl
      rw [hn,runStages,List.take_of_length_le hb] at hm
      exact hm
  · refine ⟨by scalar_tac,rfl,?_,⟨oldLayer,oldTree,hframe⟩,rfl⟩
    change sourceIndex.val = index/2^0
    simpa only [Nat.pow_zero,Nat.div_one] using hindex

end RustCrypto.FullSign
