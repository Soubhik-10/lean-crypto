module
public import RustCrypto.RecoverLayerShort
public import RustCrypto.WotsAvx2Entry
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.LayerInput
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

/-- Discharged complete layer contract for AVX2 source paths. -/
@[step] theorem recover_layer_avx2_ethlib_spec
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
  exact recover_layer_total_with_backend 256 WotsRecover.avx2_backend_contract address reader sourceIndex seed node
    layer oldLayer oldTree index hindex hframe

end RustCrypto.LayerInput
