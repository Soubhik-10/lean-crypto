module
public import RustCrypto.FullSignLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
namespace Native
open EthLib.Cryptography.Sphincs
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

@[irreducible] def layerSignature (seed : PkSeed) (secret : Seed) (key : OtsKey)
    (choice : UInt32 × Codeword) : LayerSignature key.layer :=
  ⟨choice.1,Vector.ofFn (fun chain => EthLib.Cryptography.Sphincs.chain hashId seed key chain 0 choice.2[chain].val (by simp)
      (EthLib.Cryptography.Sphincs.prf hashId seed secret (adrsPrf key chain))),EthLib.Cryptography.Sphincs.path hashId seed (EthLib.Cryptography.Sphincs.prf hashId seed secret) key.layer key.tree key.leaf⟩

@[irreducible] def nextMessage (seed : PkSeed) (secret : Seed) (key : OtsKey) (message : Digest) : Digest :=
  if key.layer = .top then message else treeRoot hashId seed (EthLib.Cryptography.Sphincs.prf hashId seed secret) key.layer key.tree

def runStages (seed : PkSeed) (secret : Seed) (index limit : Nat) : List Layer → Digest → List UInt8 → Except Nat (List UInt8)
  | [],_,written => .ok written
  | layer::rest,message,written =>
    let key := OtsKey.ofIndex layer index
    match Internal.findCounter hashId seed key message 0 limit with
    | none => .error layer.toNat
    | some choice => runStages seed secret index limit rest (nextMessage seed secret key message)
        (written ++ (encodeLayerSignature (layerSignature seed secret key choice)).data.toList)

@[irreducible] def signWithLimit (secret : Seed) (message : Message) (limit : Nat) : Except Nat (List UInt8) :=
  let seed := KeyMaterial.publicSeed secret
  let root := treeRoot hashId seed (EthLib.Cryptography.Sphincs.prf hashId seed secret) .top 0
  let rho := prfMsg hashId (KeyMaterial.secretPrf secret) seed message
  let digest := hMsg hashId rho seed root message
  let index := digestIndex digest
  let fors := forsSign hashId seed (EthLib.Cryptography.Sphincs.prf hashId seed secret) index (digestLeaves digest)
  runStages seed secret index limit stages fors.2 (rho.toList ++ (encodeFors fors.1).data.toList)

end Native

theorem layer_signature_bytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (choice : UInt32 × EthLib.Cryptography.Sphincs.Codeword) :
    (EthLib.Cryptography.Sphincs.encodeLayerSignature (Native.layerSignature (nativeNode seed) (nativeSeed secret) key choice)).data.toList =
      wotsBytes seed secret key choice ++ pathBytes seed secret key := by
  unfold Native.layerSignature EthLib.Cryptography.Sphincs.encodeLayerSignature wotsBytes pathBytes pathValues signatureValue
  simp only [ByteArray.data_append,_root_.Array.toList_append,EthLib.Base.packBytes]
  congr 1
  simp only [EthLib.Cryptography.Sphincs.packDigests,EthLib.Base.packBytes,OrderedVector.flatten_list]

theorem stages_native (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index limit : Nat)
    (remaining : List EthLib.Cryptography.Sphincs.Layer) (message : EthLib.Cryptography.Sphincs.Digest) (written : List UInt8) :
    runStages seed secret index limit remaining message written =
      Native.runStages (nativeNode seed) (nativeSeed secret) index limit remaining message written := by
  induction remaining generalizing message written with
  | nil => rfl
  | cons layer rest ih =>
    simp only [runStages,Native.runStages]
    cases hc : EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) message 0 limit with
    | none => rfl
    | some choice =>
      dsimp only
      rw [layer_signature_bytes,←List.append_assoc]
      simpa only [nextMessage,Native.nextMessage] using ih
        (nextMessage seed secret (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) message)
        (written ++ wotsBytes seed secret (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index) choice ++
          pathBytes seed secret (EthLib.Cryptography.Sphincs.OtsKey.ofIndex layer index))

end RustCrypto.FullSign
