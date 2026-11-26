module
public import RustCrypto.FullSignNative
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem bottom_index_leaf (index tree leaf : Nat) (h : index = tree*256+leaf) (hl : leaf < 256) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).leaf = leaf := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,Nat.shiftRight_eq_div_pow,EthLib.Cryptography.Sphincs.Layer.below,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT]
  norm_num only [Nat.pow_zero,Nat.div_one,Nat.reducePow]
  omega

theorem bottom_index_tree (index tree leaf : Nat) (h : index = tree*256+leaf) (hl : leaf < 256) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree = tree := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,Nat.shiftRight_eq_div_pow,EthLib.Cryptography.Sphincs.Layer.below,
    EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT]
  norm_num only [Nat.reduceAdd,Nat.reducePow]
  omega

end RustCrypto.FullSign
