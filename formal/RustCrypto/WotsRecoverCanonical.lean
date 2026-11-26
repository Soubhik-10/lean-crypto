module
public import RustCrypto.WotsRecoverLayout
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ForsRead
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def nativeValues (bytes : List U8) : Vector EthLib.Cryptography.Sphincs.Digest EthLib.Cryptography.Sphincs.Constants.V :=
  Vector.ofFn (fun chain => nativeNode (ForsRead.nodeAt bytes (16*chain.val)))

theorem ends_full (bytes : List U8) (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) : endsBefore bytes word seed key 64 =
    (EthLib.Cryptography.Sphincs.packDigests (endVector bytes word seed key)).data.toList := by
  unfold endsBefore
  have h := OrderedPrefix.prefix_full (endVector bytes word seed key) Vector.toList
  change OrderedPrefix.collect (endVector bytes word seed key) _ 64 = _ at h
  rw [h]
  simp only [EthLib.Cryptography.Sphincs.packDigests,EthLib.Base.packBytes,OrderedVector.flatten_list]

theorem ends_reference (bytes : List U8) (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) :
    Vector.ofFn (fun chain => EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key chain
      (word[chain]).val (EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH-1-(word[chain]).val)
      (by have h := (word[chain]).isLt; omega) (nativeValues bytes)[chain]) = endVector bytes word seed key := by
  unfold endVector
  apply congrArg Vector.ofFn
  funext chain
  simp only [nativeValues,Fin.getElem_fin,Vector.getElem_ofFn]
  unfold endValue
  rfl

/-- The canonical WOTS leaf is compression of the indexed recovered endpoints, after the encoding decision. -/
theorem canonical_leaf (bytes : List U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (message : EthLib.Cryptography.Sphincs.Digest) (counter : UInt32) :
    EthLib.Cryptography.Sphincs.otsLeaf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key message counter (nativeValues bytes) =
      (EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key message counter).map
        (fun word => EthLib.Cryptography.Sphincs.otsLeafHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key
          (endVector bytes word seed key)) := by
  unfold EthLib.Cryptography.Sphincs.otsLeaf
  cases hencode : EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key message counter with
  | none => rfl
  | some word =>
    simp only [Bind.bind,Pure.pure,Option.map_some]
    rw [OrderedVector.ofFnInOrder_id,ends_reference]

end RustCrypto.WotsRecover
