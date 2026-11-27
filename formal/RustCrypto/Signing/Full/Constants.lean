module
public import RustCrypto.Keygen.KeyGen
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem wots_size_spec : lean_sphincs.params.WOTS_BYTES ⦃ out => out = 1028#usize ⦄ := by
  unfold lean_sphincs.params.WOTS_BYTES
  simp only [lean_sphincs.params.WOTS_CHAINS,lean_sphincs.params.NODE_BYTES]
  step*

@[step] theorem fors_size_spec : lean_sphincs.params.FORS_BYTES ⦃ out => out = 4224#usize ⦄ := by
  unfold lean_sphincs.params.FORS_BYTES lean_sphincs.params.FORS_OPENING_BYTES
  simp only [lean_sphincs.params.FORS_TREES,lean_sphincs.params.FORS_HEIGHT,lean_sphincs.params.NODE_BYTES]
  step*

@[step] theorem counter_limit_spec : lean_sphincs.signing.COUNTER_LIMIT ⦃ out => out.val = 4294967296 ⦄ := by
  unfold lean_sphincs.signing.COUNTER_LIMIT
  step as ⟨limit,hlimit⟩
  norm_num [Nat.shiftLeft_eq,U64.size,U64.numBits,UScalarTy.numBits] at hlimit
  exact hlimit

def offset (layer : EthLib.Cryptography.Sphincs.Layer) : Nat :=
  match layer with
  | .bottom => 4240
  | .middle => 5396
  | .top => 6552

theorem layer_height_bound (layer : EthLib.Cryptography.Sphincs.Layer) : layer.height ≤ 10 := by cases layer <;> decide

theorem layer_offset_bound (layer : EthLib.Cryptography.Sphincs.Layer) : offset layer + 1028+16*layer.height ≤ 7740 := by
  cases layer <;> decide

theorem height_index (layer : EthLib.Cryptography.Sphincs.Layer) :
    lean_sphincs.params.LAYER_HEIGHTS.val[layer.toNat]! = stepWord layer.height := by
  rw [RustIndex.layer_heights_eq]
  cases layer <;> rfl

theorem layer_word_val (layer : EthLib.Cryptography.Sphincs.Layer) : (stepWord layer.toNat).val = layer.toNat := by
  cases layer <;> rfl

end RustCrypto.FullSign
