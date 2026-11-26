module
public import RustCrypto.FullSignPath
public import RustCrypto.FullSignConstants
public import RustCrypto.MessageHashFull
public import RustCrypto.DigestIndexMachine
public import RustCrypto.ForsSigningFull
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

def stages : List EthLib.Cryptography.Sphincs.Layer := [.bottom,.middle,.top]

@[irreducible] def nextMessage (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (message : EthLib.Cryptography.Sphincs.Digest) : EthLib.Cryptography.Sphincs.Digest :=
  if key.layer = .top then message else EthLib.Cryptography.Sphincs.treeRoot EthLib.Cryptography.Sphincs.hashId
    (nativeNode seed) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
    key.layer key.tree

/-- Canonical bounded signing of the remaining layers, with the first exhausted layer as the error. -/
def runStages (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index limit : Nat) :
    List EthLib.Cryptography.Sphincs.Layer → EthLib.Cryptography.Sphincs.Digest → List UInt8 → Except Nat (List UInt8)
  | [],_,written => .ok written
  | layer::rest,message,written =>
    let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index
    match EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key message 0 limit with
    | none => .error layer.toNat
    | some choice => runStages seed secret index limit rest (nextMessage seed secret key message)
        (written ++ wotsBytes seed secret key choice ++ pathBytes seed secret key)

def nativeResult : core.result.Result (Aeneas.Std.Array U8 7740#usize) lean_sphincs.signing.SignError → Except Nat (List UInt8)
  | .Ok bytes => .ok (nativeBytes bytes.val)
  | .Err (.CounterExhausted layer) => .error layer.val

@[irreducible] def initialBytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) (rho : Node) : List UInt8 :=
  (nativeNode rho).toList ++ (EthLib.Cryptography.Sphincs.encodeFors (ForsSigning.canonicalSign seed secret index digest).1).data.toList

@[irreducible] def signFromDigest (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (digest : Aeneas.Std.Array U8 34#usize) (rho : Node) (limit : Nat) : Except Nat (List UInt8) :=
  let index := EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest)
  runStages seed secret index limit stages (ForsSigning.canonicalSign seed secret index digest).2
    (initialBytes seed secret index digest rho)

theorem run_stages_nil (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index limit : Nat)
    (message : EthLib.Cryptography.Sphincs.Digest) (written : List UInt8) :
    runStages seed secret index limit [] message written = .ok written := rfl

theorem initial_bytes_length (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) (rho : Node) :
    (initialBytes seed secret index digest rho).length = 4240 := by
  unfold initialBytes
  simp only [List.length_append,Vector.length_toList]
  have hfors : (EthLib.Cryptography.Sphincs.encodeFors (ForsSigning.canonicalSign seed secret index digest).1).data.toList.length = 4224 := by
    simp [EthLib.Cryptography.Sphincs.encodeFors,EthLib.Base.packBytes,EthLib.Cryptography.Sphincs.Constants.FORS_TREES,
      EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT,EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE,
      EthLib.Cryptography.Sphincs.Constants.N]
  rw [hfors]
  rfl

theorem stage_list (layer : EthLib.Cryptography.Sphincs.Layer) :
    stages.drop layer.toNat = layer :: stages.drop (layer.toNat+1) := by cases layer <;> rfl

theorem stage_next_offset (layer : EthLib.Cryptography.Sphincs.Layer) :
    offset layer+1028+16*layer.height = if layer = .top then 7740 else offset (if layer = .bottom then .middle else .top) := by
  cases layer <;> decide

end RustCrypto.FullSign
