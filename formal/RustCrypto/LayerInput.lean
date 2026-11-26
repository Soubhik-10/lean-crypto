module
public import RustCrypto.WotsBackend
public import RustCrypto.ContextFrame
public import RustIndex
public import EthLib.Cryptography.Sphincs.Verify
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.LayerInput
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def signature (bytes : List U8) (layer : EthLib.Cryptography.Sphincs.Layer) : EthLib.Cryptography.Sphincs.LayerSignature layer :=
  ⟨WotsRecover.nativeCounter bytes,WotsRecover.nativeValues (bytes.drop 4),nativePath bytes layer.height 1028⟩

theorem height_word_val (layer : EthLib.Cryptography.Sphincs.Layer) : (stepWord layer.height).val = layer.height := by
  cases layer <;> rfl

theorem height_production (layer : EthLib.Cryptography.Sphincs.Layer) :
    stepWord layer.height ∈ lean_sphincs.params.LAYER_HEIGHTS.val := by
  rw [RustIndex.layer_heights_eq]
  cases layer <;> decide

theorem key_leaf_bound (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat) :
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf < 1024 := by
  have hmod : (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf < 2^layer.height :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hp : 2^layer.height ≤ 1024 := by cases layer <;> decide
  omega

theorem index_tree (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat) :
    (index/2^layer.below)/2^layer.height = (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,←Nat.pow_add]

theorem index_leaf (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat) :
    (index/2^layer.below)%2^layer.height = (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf := by
  simp only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,Nat.shiftRight_eq_div_pow]

theorem leaf_from_bytes (bytes : List U8) (seed message : Node) (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat)
    (hroom : 1028 ≤ bytes.length) : WotsRecover.expectedLeaf bytes seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) message =
    EthLib.Cryptography.Sphincs.otsLeaf EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) (nativeNode message) (signature bytes layer).counter
      (signature bytes layer).chainValues := by
  simp only [WotsRecover.expectedLeaf,ite_eq_left hroom,signature]

theorem canonical_layer_root (bytes : List U8) (seed message : Node) (layer : EthLib.Cryptography.Sphincs.Layer) (index : Nat)
    (hroom : 1028 ≤ bytes.length) :
    EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer index (nativeNode message)
      (signature bytes layer) =
      (WotsRecover.expectedLeaf bytes seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) message).map
        (fun leaf => EthLib.Cryptography.Sphincs.fold EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer
          (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).tree (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index).leaf leaf
          (signature bytes layer).path) := by
  unfold EthLib.Cryptography.Sphincs.layerRoot
  simp only [Bind.bind,Pure.pure]
  rw [←leaf_from_bytes bytes seed message layer index hroom]
  cases WotsRecover.expectedLeaf bytes seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) message <;> rfl

theorem consumed_success (unit : Nat) (bytes : List U8) (seed message : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (leaf : EthLib.Cryptography.Sphincs.Digest) (hroom : 1028 ≤ bytes.length)
    (hleaf : WotsRecover.expectedLeaf bytes seed key message = some leaf) :
    WotsRecover.consumed unit bytes seed key message = 1028 := by
  have hencoding : (WotsRecover.encoding bytes seed key message).isNone = false := by
    cases he : WotsRecover.encoding bytes seed key message with
    | none =>
      have hn := WotsRecover.no_encoding_leaf bytes seed key message he
      rw [hn] at hleaf
      contradiction
    | some word => rfl
  simp only [WotsRecover.consumed,ite_eq_right (show ¬bytes.length < 4 by omega),hencoding,
    Bool.false_eq_true,ite_false,ite_eq_left hroom]

theorem path_reader (bytes : List U8) (count : Nat) (hroom : 1028+16*count ≤ bytes.length) :
    bytes.drop 1028 = nodesBytes (nodeList bytes count 1028) ++ bytes.drop (1028+16*count) := by
  rw [serialized_nodes bytes count 1028 hroom]
  have hd : bytes.drop (1028+16*count) = (bytes.drop 1028).drop (16*count) := by rw [List.drop_drop]
  rw [hd,List.take_append_drop]

end RustCrypto.LayerInput
