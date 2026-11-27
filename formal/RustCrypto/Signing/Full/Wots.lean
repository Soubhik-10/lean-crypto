module
public import RustCrypto.Wots.Signing.Full
public import RustCrypto.Tree.Primitives
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

def nativeBytes (bytes : List U8) : List UInt8 := bytes.map (fun b => UInt8.ofBitVec b.bv)

@[irreducible] def wotsBytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (choice : UInt32 × EthLib.Cryptography.Sphincs.Codeword) : List UInt8 :=
  (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN choice.1.toNat).toList ++
    (EthLib.Cryptography.Sphincs.packDigests (Vector.ofFn (signatureValue seed secret key choice.2))).data.toList

@[irreducible] def wotsResult (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) (limit : U64) (original : Slice U8)
    (out : Option Unit × Address × Slice U8) : Prop :=
  match EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key
      (nativeNode message) 0 limit.val with
  | none => out.1 = none ∧ out.2.2 = original ∧ TreePrimitives.frame out.2.1 seed key.layer key.tree
  | some choice => out.1 = some () ∧ nativeBytes out.2.2.val = wotsBytes seed secret key choice ++
      (nativeBytes original.val).drop 1028 ∧ TreePrimitives.frame out.2.1 seed key.layer key.tree

@[step] theorem wots_sign_spec (address : Address) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (message : Node) (output : Slice U8) (limit : U64)
    (hframe : TreePrimitives.frame address seed key.layer key.tree) (hsize : 1028 ≤ output.val.length) :
    lean_sphincs.wots.sign address secret (stepWord key.leaf) message output limit ⦃ out =>
      wotsResult seed secret key message limit output out ⦄ := by
  rcases hframe with ⟨tag,pair,word2,word3,hhead⟩
  have hh : address.val.take 48 = headBytes seed (stepWord key.layer.toNat) (treeWord key.tree)
      tag pair (stepWord word2.val) (stepWord word3.val) := by
    simpa only [TreePrimitives.rebuild_word] using hhead
  apply WP.spec_mono (sign_any_pair_ethlib_spec address seed secret key message output limit tag pair word2.val word3.val hh hsize)
  intro out hout
  unfold wotsResult
  generalize hc : EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
    (nativeNode seed) key (nativeNode message) 0 limit.val = choice at hout ⊢
  cases choice with
  | none =>
    simp only [signingResult] at hout
    refine ⟨hout.1,hout.2.1,7#u32,stepWord key.leaf,stepWord 0,stepWord 0,?_⟩
    exact hout.2.2
  | some choice =>
    rcases choice with ⟨counter,code⟩
    simp only [signingResult] at hout
    rcases hout with ⟨hstatus,hbytes,tag,w2,w3,hnext⟩
    refine ⟨hstatus,?_,tag,stepWord key.leaf,stepWord w2,stepWord w3,hnext⟩
    simpa only [nativeBytes,wotsBytes,Vector.toList] using hbytes

theorem wots_bytes_length (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (choice : UInt32 × EthLib.Cryptography.Sphincs.Codeword) :
    (wotsBytes seed secret key choice).length = 1028 := by
  simp [wotsBytes,EthLib.Cryptography.Sphincs.packDigests,EthLib.Base.packBytes,
    EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN,EthLib.Cryptography.Sphincs.Constants.V,
    EthLib.Cryptography.Sphincs.Constants.N]

end RustCrypto.FullSign
