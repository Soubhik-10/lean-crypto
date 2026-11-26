module
public import RustCrypto.RecoverLayerShort
public import RustCrypto.MessageHashFull
public import RustCrypto.DigestIndexMachine
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

def publicKey (key : Aeneas.Std.Array U8 32#usize) : EthLib.Cryptography.Sphincs.PublicKey :=
  ⟨nativeNode (MessageHashBridge.keySeed key),nativeNode (MessageHashBridge.keyRoot key)⟩

def signature (bytes : List U8) : EthLib.Cryptography.Sphincs.Signature where
  randomizer := nativeNode (ForsRead.nodeAt bytes 0)
  fors := ForsRead.decodedOpenings (bytes.drop 16)
  bottom := LayerInput.signature (bytes.drop 4240) .bottom
  middle := LayerInput.signature (bytes.drop 5396) .middle
  top := LayerInput.signature (bytes.drop 6552) .top

def layerRoots (seed : EthLib.Cryptography.Sphincs.PkSeed) (index : Nat) (message : EthLib.Cryptography.Sphincs.Digest)
    (bottomSig : EthLib.Cryptography.Sphincs.LayerSignature .bottom)
    (middleSig : EthLib.Cryptography.Sphincs.LayerSignature .middle)
    (topSig : EthLib.Cryptography.Sphincs.LayerSignature .top) : Option EthLib.Cryptography.Sphincs.Digest :=
  match EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId seed .bottom index message bottomSig with
  | none => none
  | some bottom =>
    match EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId seed .middle index bottom middleSig with
    | none => none
    | some middle => EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId seed .top index middle topSig

@[irreducible] def referenceRoot (key : EthLib.Cryptography.Sphincs.PublicKey) (message : EthLib.Cryptography.Sphincs.Message)
    (sig : EthLib.Cryptography.Sphincs.Signature) : Option EthLib.Cryptography.Sphincs.Digest :=
  let digest := EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.hashId sig.randomizer key.pkSeed key.root message
  let index := EthLib.Cryptography.Sphincs.digestIndex digest
  let forsKey := EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.hashId key.pkSeed index
    (EthLib.Cryptography.Sphincs.digestLeaves digest) sig.fors
  layerRoots key.pkSeed index forsKey sig.bottom sig.middle sig.top

theorem reference_from_digest (key : EthLib.Cryptography.Sphincs.PublicKey) (message : EthLib.Cryptography.Sphincs.Message)
    (sig : EthLib.Cryptography.Sphincs.Signature) (digest : EthLib.Cryptography.Sphincs.MessageDigest)
    (hdigest : EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.hashId sig.randomizer key.pkSeed key.root message = digest) :
    referenceRoot key message sig = layerRoots key.pkSeed (EthLib.Cryptography.Sphincs.digestIndex digest)
      (EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.hashId key.pkSeed
        (EthLib.Cryptography.Sphincs.digestIndex digest) (EthLib.Cryptography.Sphincs.digestLeaves digest) sig.fors)
      sig.bottom sig.middle sig.top := by
  unfold referenceRoot
  simp only [hdigest]

theorem verify_reference_root (key : EthLib.Cryptography.Sphincs.PublicKey) (message : EthLib.Cryptography.Sphincs.Message)
    (sig : EthLib.Cryptography.Sphincs.Signature) :
    EthLib.Cryptography.Sphincs.verifyWith EthLib.Cryptography.Sphincs.hashId key message sig =
      ((referenceRoot key message sig).map (fun root => decide (root = key.root))).getD false := by
  let digest := EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.hashId sig.randomizer key.pkSeed key.root message
  let index := EthLib.Cryptography.Sphincs.digestIndex digest
  let forsKey := EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.hashId key.pkSeed index
    (EthLib.Cryptography.Sphincs.digestLeaves digest) sig.fors
  cases h0 : EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId key.pkSeed .bottom index forsKey sig.bottom with
  | none =>
    simp only [digest,index,forsKey] at h0
    unfold referenceRoot layerRoots EthLib.Cryptography.Sphincs.verifyWith
    simp only [Bind.bind,Pure.pure,h0,Option.map_none,Option.getD_none]
  | some bottom =>
    cases h1 : EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId key.pkSeed .middle index bottom sig.middle with
    | none =>
      simp only [digest,index,forsKey] at h0
      simp only [digest,index] at h1
      unfold referenceRoot layerRoots EthLib.Cryptography.Sphincs.verifyWith
      simp only [Bind.bind,Pure.pure,h0,h1,Option.map_none,Option.getD_none]
    | some middle =>
      cases h2 : EthLib.Cryptography.Sphincs.layerRoot EthLib.Cryptography.Sphincs.hashId key.pkSeed .top index middle sig.top with
      | none =>
        simp only [digest,index,forsKey] at h0
        simp only [digest,index] at h1 h2
        unfold referenceRoot layerRoots EthLib.Cryptography.Sphincs.verifyWith
        simp only [Bind.bind,Pure.pure,h0,h1,h2,Option.map_none,Option.getD_none]
      | some root =>
        simp only [digest,index,forsKey] at h0
        simp only [digest,index] at h1 h2
        unfold referenceRoot layerRoots EthLib.Cryptography.Sphincs.verifyWith
        simp only [Bind.bind,Pure.pure,h0,h1,h2,Option.map_some,Option.getD_some]

def ForsContract : Prop :=
  ∀ (address : Address) (reader : Slice U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (index : Nat),
    TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree →
    lean_sphincs.fors.recover_fors address reader digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).leaf) ⦃ out =>
      out.1.map nativeNode = (if 4224 ≤ reader.val.length then some
        (EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.hashId (nativeNode seed) index
          (EthLib.Cryptography.Sphincs.digestLeaves (ForsDigest.nativeDigest digest)) (ForsRead.decodedOpenings reader.val)) else none) ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree ∧
      (out.1.isSome → out.2.2.val = reader.val.drop 4224) ⦄

def RootContract : Prop :=
  ∀ (key message : Aeneas.Std.Array U8 32#usize) (bytes : Slice U8), bytes.val.length = 7740 →
    lean_sphincs.verifier.recover_root key message bytes ⦃ out =>
      out.map nativeNode = referenceRoot (publicKey key) (nativeSeed message) (signature bytes.val) ⦄

def expectedRoot (key message : Aeneas.Std.Array U8 32#usize) (bytes : List U8) : Option EthLib.Cryptography.Sphincs.Digest :=
  if bytes.length = 7740 then referenceRoot (publicKey key) (nativeSeed message) (signature bytes) else none

def expectedVerify (key message : Aeneas.Std.Array U8 32#usize) (bytes : List U8) : Bool :=
  if bytes.length = 7740 then EthLib.Cryptography.Sphincs.verifyWith EthLib.Cryptography.Sphincs.hashId
    (publicKey key) (nativeSeed message) (signature bytes) else false

theorem expected_verify_root (key message : Aeneas.Std.Array U8 32#usize) (bytes : List U8) :
    expectedVerify key message bytes = ((expectedRoot key message bytes).map
      (fun root => decide (root = (publicKey key).root))).getD false := by
  unfold expectedVerify expectedRoot
  split
  · exact verify_reference_root _ _ _
  · rfl

end RustCrypto.WholeVerifier
