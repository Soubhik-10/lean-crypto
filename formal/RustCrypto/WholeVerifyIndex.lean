module
public import RustCrypto.WholeVerifyModel
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.WotsEthlib RustCrypto.TweakableBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem digest_bottom_tree (digest : Aeneas.Std.Array U8 34#usize) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom (EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest))).tree =
      MessageHashBridge.rawTree digest := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,EthLib.Cryptography.Sphincs.Layer.below,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT,Nat.shiftRight_eq_div_pow,
    MessageHashBridge.digest_index_native]
  have hl := MessageHashBridge.raw_leaf_bound digest
  omega

theorem digest_bottom_leaf (digest : Aeneas.Std.Array U8 34#usize) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom (EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest))).leaf =
      MessageHashBridge.rawLeaf digest := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,EthLib.Cryptography.Sphincs.Layer.below,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT,Nat.shiftRight_eq_div_pow,
    MessageHashBridge.digest_index_native]
  have hl := MessageHashBridge.raw_leaf_bound digest
  omega

theorem read_array_eq {α : Type} [Inhabited α] {n : Usize} (values : Aeneas.Std.Array α n) (index : Usize)
    (hindex : index.val < n.val) : values.index_usize index = .ok (values[index.val]!) := by
  unfold Aeneas.Std.Array.index_usize
  rw [Aeneas.Std.Array.getElem?_Usize_eq]
  rw [getElem?_pos values.val index.val (by scalar_tac)]
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos values.val index.val (by scalar_tac)]

theorem bottom_height_eq : Aeneas.Std.Array.index_usize lean_sphincs.params.LAYER_HEIGHTS 0#usize =
    .ok (stepWord EthLib.Cryptography.Sphincs.Layer.bottom.height) := by
  rw [read_array_eq _ _ (by scalar_tac)]
  simp only [Aeneas.Std.Array.getElem!_Nat_eq,RustIndex.layer_heights_eq]
  rfl

theorem middle_height_eq : Aeneas.Std.Array.index_usize lean_sphincs.params.LAYER_HEIGHTS 1#usize =
    .ok (stepWord EthLib.Cryptography.Sphincs.Layer.middle.height) := by
  rw [read_array_eq _ _ (by scalar_tac)]
  simp only [Aeneas.Std.Array.getElem!_Nat_eq,RustIndex.layer_heights_eq]
  rfl

theorem top_height_eq : Aeneas.Std.Array.index_usize lean_sphincs.params.LAYER_HEIGHTS 2#usize =
    .ok (stepWord EthLib.Cryptography.Sphincs.Layer.top.height) := by
  rw [read_array_eq _ _ (by scalar_tac)]
  simp only [Aeneas.Std.Array.getElem!_Nat_eq,RustIndex.layer_heights_eq]
  rfl

end RustCrypto.WholeVerifier
