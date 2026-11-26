module
public import RustCrypto.WotsEntry
public import RustCrypto.WotsScalarChains
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem scalar_backend_contract : ChainsContract 16 := by
  intro address reader ends digits word seed key hdigits hframe
  exact scalar_chains_total_spec address reader ends digits word seed key hdigits hframe

/-- Complete actual non-AVX2 WOTS recovery: counter parsing, encoding rejection, chains, compression and every short input. -/
@[step] theorem recover_wots_scalar_ethlib_spec (address : Address) (reader : Slice U8) (message seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (hframe : TreePrimitives.frame address seed key.layer key.tree) :
    lean_sphincs.wots.recover_wots address reader (stepWord key.leaf) message ⦃ out =>
      out.1.map nativeNode = expectedLeaf reader.val seed key message ∧
      TreePrimitives.frame out.2.1 seed key.layer key.tree ∧
      out.2.2.val = reader.val.drop (consumed 16 reader.val seed key message) ⦄ := by
  exact entry_with_backend 16 scalar_backend_contract address reader message seed key hframe

end RustCrypto.WotsRecover
