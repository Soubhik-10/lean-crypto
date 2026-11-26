module
public import RustCrypto.RecoverLayer
public import RustCrypto.LayerIndex
public import RustCrypto.ClimbShort
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.LayerInput
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

/-- Every truncated layer is rejected, including counters, WOTS values and incomplete authentication paths. -/
@[step] theorem recover_layer_short_with_backend (unit : Nat) (backend : WotsRecover.ChainsContract unit)
    (address : Address) (reader : Slice U8) (sourceIndex : U64) (seed node : Node)
    (layer oldLayer : EthLib.Cryptography.Sphincs.Layer) (oldTree index : Nat)
    (hindex : sourceIndex.val = index/2^layer.below) (hshort : reader.val.length < 1028+16*layer.height)
    (hframe : TreePrimitives.frame address seed oldLayer oldTree) :
    lean_sphincs.verifier.recover_layer address reader sourceIndex (stepWord layer.toNat) (stepWord layer.height) node ⦃ out =>
      out.1 = none ∧ TreePrimitives.frame out.2.1 seed layer (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      out.2.2.2.val = (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
  unfold lean_sphincs.verifier.recover_layer
  step with take_layer_typed_spec sourceIndex layer index hindex as ⟨leaf,nextIndex,hleaf,htree,htreeVal⟩
  rw [hleaf]
  have hset := ContextFrame.set_tree_frame_spec address seed oldLayer layer oldTree key.tree hframe
  rw [←htree] at hset
  step with hset as ⟨layerAddress,hlayerFrame⟩
  step with WotsRecover.entry_with_backend unit backend layerAddress reader node seed key hlayerFrame
    as ⟨leafOption,afterWots,afterWotsReader,hwots,hwotsFrame,hwotsReader⟩
  cases leafOption with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
    exact ⟨True.intro,hwotsFrame,htreeVal⟩
  | some wotsLeaf =>
    have hexpected : WotsRecover.expectedLeaf reader.val seed key node = some (nativeNode wotsLeaf) := by
      simpa only [Option.map_some] using hwots.symm
    have hroom : 1028 ≤ reader.val.length := by
      by_contra h
      have hn : WotsRecover.expectedLeaf reader.val seed key node = none := by
        simp only [WotsRecover.expectedLeaf,ite_eq_right h]
      rw [hn] at hexpected
      contradiction
    have hconsumed := consumed_success unit reader.val seed node key (nativeNode wotsLeaf) hroom hexpected
    rw [hconsumed] at hwotsReader
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok,lean_sphincs.verifier.HYPERTREE]
    step with ForsPrimitives.domain_frame_spec afterWots seed layer key.tree 2#u32 0#u32 hwotsFrame
      as ⟨treeAddress,htreeAddress⟩
    have hclimbFrame : keyFrame treeAddress seed ⟨layer,key.tree,0⟩ .tree := by
      refine ⟨0#u32,0#u32,?_⟩
      have htag : addressTag .tree = 2#u32 := rfl
      have hz : stepWord 0 = 0#u32 := rfl
      simpa only [htag,hz] using htreeAddress
    have hheight : (stepWord layer.height).val ≤ 10 := by rw [height_word_val]; cases layer <;> decide
    have hpathShort : afterWotsReader.val.length < 16*(stepWord layer.height).val := by
      rw [hwotsReader,List.length_drop,height_word_val]
      omega
    step with climb_key_short_spec treeAddress afterWotsReader (stepWord key.leaf) (stepWord layer.height) wotsLeaf seed
      ⟨layer,key.tree,0⟩ .tree hheight hpathShort hclimbFrame
      as ⟨rootOption,finalAddress,finalReader,hroot,hfinalReader,hfinalFrame⟩
    refine ⟨hroot,?_,htreeVal⟩
    rcases hfinalFrame with ⟨word2,word3,hhead⟩
    exact ⟨addressTag .tree,stepWord 0,word2,word3,hhead⟩

/-- Total layer refinement for every byte length and all three production layers. -/
@[step] theorem recover_layer_total_with_backend (unit : Nat) (backend : WotsRecover.ChainsContract unit)
    (address : Address) (reader : Slice U8) (sourceIndex : U64) (seed node : Node)
    (layer oldLayer : EthLib.Cryptography.Sphincs.Layer) (oldTree index : Nat)
    (hindex : sourceIndex.val = index/2^layer.below) (hframe : TreePrimitives.frame address seed oldLayer oldTree) :
    lean_sphincs.verifier.recover_layer address reader sourceIndex (stepWord layer.toNat) (stepWord layer.height) node ⦃ out =>
      out.1.map nativeNode = (if 1028+16*layer.height ≤ reader.val.length then
        EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer index (nativeNode node)
          (signature reader.val layer) else none) ∧
      TreePrimitives.frame out.2.1 seed layer (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      out.2.2.2.val = (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      (out.1.isSome → out.2.2.1.val = reader.val.drop (1028+16*layer.height)) ⦄ := by
  by_cases hroom : 1028+16*layer.height ≤ reader.val.length
  · apply WP.spec_mono (recover_layer_with_backend unit backend address reader sourceIndex seed node layer oldLayer oldTree index hindex hroom hframe)
    intro out hout
    simpa only [ite_eq_left hroom] using hout
  · apply WP.spec_mono (recover_layer_short_with_backend unit backend address reader sourceIndex seed node layer oldLayer oldTree index hindex (by omega) hframe)
    rintro out ⟨hresult,hnextFrame,hnextIndex⟩
    refine ⟨?_,hnextFrame,hnextIndex,?_⟩
    · simp only [ite_eq_right hroom,hresult,Option.map_none]
    · simp only [hresult,Option.isSome_none,Bool.false_eq_true,false_implies]

end RustCrypto.LayerInput
