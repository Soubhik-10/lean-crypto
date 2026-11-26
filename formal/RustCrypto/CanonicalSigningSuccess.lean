module
public import RustCrypto.CanonicalSigning
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
open EthLib.Cryptography.Sphincs
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] hMsg forsRecover layerRoot treeRoot prfMsg

/-- For every counter limit, successful native signing produces exactly a typed signature that verifies. -/
theorem native_sign_success (secret : Seed) (message : Message) (limit : Nat) (written : List UInt8)
    (successful : FullSign.Native.signWithLimit secret message limit = .ok written) :
    ∃ sig : Signature, written = (encodeSignature sig).data.toList ∧
      verifyWith hashId (KeyGen.publicKey secret) message sig = true := by
  let seed := KeyMaterial.publicSeed secret
  let root := treeRoot hashId seed (prf hashId seed secret) .top 0
  let rho := prfMsg hashId (KeyMaterial.secretPrf secret) seed message
  let digest := hMsg hashId rho seed root message
  let index := digestIndex digest
  let fors := forsSign hashId seed (prf hashId seed secret) index (digestLeaves digest)
  unfold FullSign.Native.signWithLimit at successful
  change FullSign.Native.runStages seed secret index limit FullSign.stages fors.2
    (rho.toList ++ (encodeFors fors.1).data.toList) = .ok written at successful
  simp only [FullSign.stages,FullSign.Native.runStages] at successful
  cases h0 : Internal.findCounter hashId seed (OtsKey.ofIndex .bottom index) fors.2 0 limit with
  | none => simp only [h0,reduceCtorEq] at successful
  | some bottom =>
    simp only [h0,lower_next_bottom] at successful
    cases h1 : Internal.findCounter hashId seed (OtsKey.ofIndex .middle index)
      (treeRoot hashId seed (prf hashId seed secret) .bottom (OtsKey.ofIndex .bottom index).tree) 0 limit with
    | none => simp only [h1,reduceCtorEq] at successful
    | some middle =>
      simp only [h1,lower_next_middle] at successful
      cases h2 : Internal.findCounter hashId seed (OtsKey.ofIndex .top index)
        (treeRoot hashId seed (prf hashId seed secret) .middle (OtsKey.ofIndex .middle index).tree) 0 limit with
      | none => simp only [h2,reduceCtorEq] at successful
      | some top =>
        simp only [h2] at successful
        let sig := signingSignature seed secret index rho fors.1 bottom middle top
        refine ⟨sig,?_,?_⟩
        · rw [signature_encoded_list]
          exact (Except.ok.inj successful).symm
        · have hv := signing_signature_verifies seed secret message rho digest index limit rfl rfl bottom middle top h0 h1 h2
          unfold KeyGen.publicKey
          exact hv

end RustCrypto.CanonicalCorrectness
