module
public import RustCrypto.Verification.Layer.Input
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.LayerInput
open RustCrypto.WotsChain RustCrypto.WotsEthlib RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem take_layer_typed_spec (sourceIndex : U64) (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat)
    (hindex : sourceIndex.val = index/2^layer.below) :
    lean_sphincs.params.take_layer sourceIndex (stepWord layer.height) ⦃ out =>
      out.1 = stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf ∧
      out.2 = treeWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ∧
      out.2.val = (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
  have hbound : key.leaf < 1024 := key_leaf_bound layer index
  apply WP.spec_mono (RustIndex.take_layer_production_spec sourceIndex (stepWord layer.height) (height_production layer))
  rintro ⟨leaf,nextIndex⟩ ⟨hleaf,hnextIndex⟩
  have hl : leaf.val = key.leaf := by
    rw [hleaf,height_word_val,hindex]
    exact index_leaf layer index
  have ht : nextIndex.val = key.tree := by
    rw [hnextIndex,height_word_val,hindex]
    exact index_tree layer index
  refine ⟨?_,?_,ht⟩
  · apply UScalar.eq_of_val_eq
    exact hl.trans (step_word_value key.leaf (by omega)).symm
  · apply UScalar.eq_of_val_eq
    change nextIndex.val = key.tree%18446744073709551616
    rw [Nat.mod_eq_of_lt (by rw [←ht]; scalar_tac)]
    exact ht

end RustCrypto.LayerInput
