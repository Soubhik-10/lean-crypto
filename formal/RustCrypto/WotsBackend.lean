module
public import RustCrypto.WotsEncodingRead
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

/-- Explicit contract shared by the scalar and AVX2 source implementations. -/
def ChainsContract (unit : Nat) : Prop :=
  ∀ (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey),
    digitRelation digits word → keyFrame address seed key .wotsHash →
    lean_sphincs.wots.recover_chains address reader digits ends ⦃ out =>
      out.1 = (if 1024 ≤ reader.val.length then some () else none) ∧ keyFrame out.2.1 seed key .wotsHash ∧
      out.2.2.1.val = reader.val.drop (if 1024 ≤ reader.val.length then 1024 else unit*(reader.val.length/unit)) ∧
      (1024 ≤ reader.val.length → nativeBytes out.2.2.2 = nativeBytes ends ++ endsBefore reader.val word seed key 64) ⦄

theorem no_encoding_leaf (bytes : List U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node)
    (hencoding : encoding bytes seed key message = none) : expectedLeaf bytes seed key message = none := by
  unfold expectedLeaf
  split
  · rw [canonical_leaf]
    change (encoding bytes seed key message).map _ = none
    simp only [hencoding,Option.map_none]
  · rfl

theorem encoding_leaf (bytes : List U8) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node)
    (word : EthLib.Cryptography.Sphincs.Codeword) (hroom : 1028 ≤ bytes.length)
    (hencoding : encoding bytes seed key message = some word) : expectedLeaf bytes seed key message =
      some (EthLib.Cryptography.Sphincs.otsLeafHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key
        (endVector (bytes.drop 4) word seed key)) := by
  unfold expectedLeaf
  rw [ite_eq_left hroom,canonical_leaf]
  change (encoding bytes seed key message).map _ = _
  simp only [hencoding,Option.map_some]

end RustCrypto.WotsRecover
