module
public import RustCrypto.LayerInput
public import RustCrypto.WotsEntry
public import RustCrypto.ForsPrimitives
public import RustCrypto.ClimbBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.LayerInput
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

/-- One complete actual hypertree layer: index splitting, WOTS rejection/recovery, and path climbing. -/
@[step] theorem recover_layer_with_backend (unit : Nat) (backend : WotsRecover.ChainsContract unit)
    (address : Address) (reader : Slice U8) (sourceIndex : U64) (seed node : Node)
    (layer oldLayer : EthLib.Cryptography.Sphincs.Layer) (oldTree index : Nat)
    (hindex : sourceIndex.val = index/2^layer.below)
    (hreader : 1028+16*layer.height ≤ reader.val.length)
    (hframe : TreePrimitives.frame address seed oldLayer oldTree) :
    lean_sphincs.verifier.recover_layer address reader sourceIndex (stepWord layer.toNat) (stepWord layer.height) node ⦃ out =>
      out.1.map nativeNode = EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) layer index (nativeNode node) (signature reader.val layer) ∧
      TreePrimitives.frame out.2.1 seed layer (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      out.2.2.2.val = (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      (out.1.isSome → out.2.2.1.val = reader.val.drop (1028+16*layer.height)) ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
  have hkeyBound : key.leaf < 1024 := key_leaf_bound layer index
  have hkeyWord : (stepWord key.leaf).val = key.leaf := step_word_value key.leaf (by omega)
  have hroom : 1028 ≤ reader.val.length := by omega
  unfold lean_sphincs.verifier.recover_layer
  step with RustIndex.take_layer_production_spec sourceIndex (stepWord layer.height) (height_production layer)
    as ⟨leaf,nextIndex,hleaf,hnextIndex⟩
  have hl : leaf.val = key.leaf := by
    rw [hleaf,height_word_val,hindex]
    exact index_leaf layer index
  have ht : nextIndex.val = key.tree := by
    rw [hnextIndex,height_word_val,hindex]
    exact index_tree layer index
  have hleafWord : leaf = stepWord key.leaf := by
    apply UScalar.eq_of_val_eq
    exact hl.trans hkeyWord.symm
  have htreeWord : nextIndex = treeWord key.tree := by
    apply UScalar.eq_of_val_eq
    change nextIndex.val = key.tree%18446744073709551616
    rw [Nat.mod_eq_of_lt (by rw [←ht]; scalar_tac)]
    exact ht
  rw [hleafWord]
  have hset := ContextFrame.set_tree_frame_spec address seed oldLayer layer oldTree key.tree hframe
  rw [←htreeWord] at hset
  step with hset as ⟨layerAddress,hlayerFrame⟩
  step with WotsRecover.entry_with_backend unit backend layerAddress reader node seed key hlayerFrame
    as ⟨leafOption,afterWots,afterWotsReader,hwots,hwotsFrame,hwotsReader⟩
  have hcanonical := canonical_layer_root reader.val seed node layer index hroom
  rw [←hwots] at hcanonical
  cases leafOption with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
    refine ⟨?_,hwotsFrame,ht,?_⟩
    · simpa only [Option.map_none] using hcanonical.symm
    · simp only [Option.isSome_none,Bool.false_eq_true,false_implies]
  | some wotsLeaf =>
    have hexpected : WotsRecover.expectedLeaf reader.val seed key node = some (nativeNode wotsLeaf) := by
      simpa only [Option.map_some] using hwots.symm
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
    have hpathReader : afterWotsReader.val = nodesBytes (nodeList reader.val layer.height 1028) ++
        reader.val.drop (1028+16*layer.height) := hwotsReader.trans (path_reader reader.val layer.height hreader)
    step with climb_xmss_ethlib_spec treeAddress afterWotsReader (stepWord key.leaf) (stepWord layer.height) wotsLeaf seed layer key.tree
      (nodeList reader.val layer.height 1028) (reader.val.drop (1028+16*layer.height))
      (by simp only [nodeList_length,height_word_val]) hclimbFrame hpathReader
      as ⟨rootOption,finalAddress,finalReader,hroot,hfinalReader,hfinalFrame⟩
    have hleafVal : (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf).val =
        (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf := hkeyWord
    have hrootFold : rootOption.map nativeNode = some (EthLib.Cryptography.Sphincs.fold EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) layer key.tree key.leaf (nativeNode wotsLeaf) (signature reader.val layer).path) := by
      simpa only [hleafVal,EthLib.Cryptography.Sphincs.fold,signature,nativePath_list,key] using hroot
    refine ⟨?_,?_,ht,fun _ => hfinalReader⟩
    · exact hrootFold.trans (by simpa only [Option.map_some] using hcanonical.symm)
    · rcases hfinalFrame with ⟨word2,word3,hhead⟩
      exact ⟨addressTag .tree,stepWord 0,word2,word3,hhead⟩

end RustCrypto.LayerInput
