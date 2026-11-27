module
public import RustCrypto.Wots.Avx2.Positions
public import RustCrypto.Wots.Avx2.Gather
public import RustCrypto.Wots.Avx2.Scatter
public import RustCrypto.Wots.Avx2.Step
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem group_prefix_native (address : Address) (selected offset : Usize) (step : U8) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (hselected : selected.val < 16) (hoffset : offset.val+16 ≤ 64)
    (hframe : keyFrame address seed key .wotsHash) :
    ((groupAddress address selected offset step).val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.keyAdrs .wotsHash key (offset.val+selected.val) step.val).toList := by
  rcases hframe with ⟨old2,old3,hhead⟩
  have hp := positioned_frame address seed (stepWord key.layer.toNat) (treeWord key.tree) (addressTag .wotsHash)
    (stepWord key.leaf) old2 old3 (stepWord (offset.val+selected.val)) (stepWord step.val) hhead
  unfold groupAddress
  rw [hp]
  have hglobal := step_word_value (offset.val+selected.val) (by omega)
  have hstep := step_word_value step.val (by scalar_tac)
  simpa only [hglobal,hstep] using ForsPrimitives.typed_position_head seed key (addressTag .wotsHash) .wotsHash
    (stepWord (offset.val+selected.val)) (stepWord step.val) (native_tag .wotsHash)

theorem group_positioned_frame (address : Address) (selected offset : Usize) (step : U8) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (hframe : keyFrame address seed key .wotsHash) :
    keyFrame (groupAddress address selected offset step) seed key .wotsHash := by
  rcases hframe with ⟨old2,old3,hhead⟩
  refine ⟨stepWord (offset.val+selected.val),stepWord step.val,?_⟩
  exact positioned_frame address seed (stepWord key.layer.toNat) (treeWord key.tree) (addressTag .wotsHash)
    (stepWord key.leaf) old2 old3 (stepWord (offset.val+selected.val)) (stepWord step.val) hhead

/-- The complete actual four-lane group hashes selected original values and scatters results in source order. -/
@[step] theorem recover_group_spec (addresses : Aeneas.Std.Array Address 4#usize)
    (nodes : Aeneas.Std.Array Node 16#usize) (chains : Aeneas.Std.Array Usize 4#usize) (offset : Usize) (step : U8)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) (hoffset : offset.val+16 ≤ 64)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_group addresses nodes chains offset step ⦃ out =>
      ∃ values : Aeneas.Std.Array Node 4#usize,
        out.2 = scatter chains values 4 0 nodes ∧
        (∀ j < 4, nativeNode (values[j]!) = chainHash seed key (offset.val+(chains[j]!).val) step.val
          (nativeNode (nodes[(chains[j]!).val]!))) ∧
        (∀ j < 4, keyFrame (out.1[j]!) seed key .wotsHash) ⦄ := by
  unfold lean_sphincs.wots.recover_group
  step with position_group_spec addresses chains offset step hchains hoffset as ⟨positioned,hpositioned⟩
  step with gather_array_spec nodes chains hchains as ⟨gathered,hgathered⟩
  step with RustCrypto.BatchNodes.hash_nodes_spec positioned gathered as ⟨values,nextAddresses,hvalues,hnextAddresses⟩
  step with scatter_loop_spec nodes chains values 0#usize (by decide) hchains as ⟨nextNodes,hscatter⟩
  refine ⟨values,hscatter,?_,?_⟩
  · intro j hj
    have hp : ((positioned[j]!).val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
        (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.keyAdrs .wotsHash key (offset.val+(chains[j]!).val) step.val).toList := by
      rw [hpositioned j hj]
      exact group_prefix_native (addresses[j]!) (chains[j]!) offset step seed key (hchains j hj) hoffset (hframes j hj)
    have hinput : RustCrypto.bytes ((positioned[j]!).val.take 48 ++ (gathered[j]!).val) =
        EthLib.Cryptography.Sphincs.thInput (nativeNode seed)
          (EthLib.Cryptography.Sphincs.keyAdrs .wotsHash key (offset.val+(chains[j]!).val) step.val)
          (EthLib.Base.packBytes (nativeNode (nodes[(chains[j]!).val]!))) := by
      rw [hgathered j hj]
      exact node_preimage (positioned[j]!) (nodes[(chains[j]!).val]!) (nativeNode seed) _ hp
    apply Vector.toList_inj.1
    rw [native_node_list,hvalues j hj,List.map_take,ByteBridge.digest_native]
    unfold chainHash
    rw [th_pure_list,hinput]
  · intro j hj
    have hp : keyFrame (positioned[j]!) seed key .wotsHash := by
      rw [hpositioned j hj]
      exact group_positioned_frame (addresses[j]!) (chains[j]!) offset step seed key (hframes j hj)
    rcases hp with ⟨word2,word3,hhead⟩
    refine ⟨word2,word3,?_⟩
    calc
      _ = (positioned[j]!).val.take 48 := by
        rw [hnextAddresses j hj]
        simp [List.setSlice!,List.take_of_length_le]
      _ = _ := hhead

end RustCrypto.WotsAvx2
