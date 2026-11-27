module
public import RustCrypto.Signing.Full.Native
public import RustCrypto.Correctness.Wots
public import RustCrypto.Correctness.Trees
public import RustCrypto.Correctness.Signing.Serialization
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
open EthLib.Cryptography.Sphincs
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] hMsg forsRecover layerRoot

theorem digest_index_bounded (digest : MessageDigest) : digestIndex digest < 67108864 := by
  have ht : digestTree digest < 262144 := Nat.mod_lt _ (by decide)
  have hl : digestLeaf digest < 256 := Nat.mod_lt _ (by decide)
  unfold digestIndex
  change digestTree digest*256+digestLeaf digest < 67108864
  omega

theorem top_tree_zero (index : Nat) (hb : index < 67108864) : (OtsKey.ofIndex .top index).tree = 0 := by
  simp only [OtsKey.ofIndex,Nat.shiftRight_eq_div_pow,Layer.below,Layer.height,Constants.LOWER_HEIGHT,Constants.TOP_HEIGHT]
  exact Nat.div_eq_of_lt hb

/-- The path attached to each successful WOTS signature recovers that exact tree's root. -/
theorem layer_signature_root (seed : PkSeed) (secret : Seed) (layer : Layer) (index : Nat)
    (message : Digest) (limit : Nat) (choice : UInt32 × Codeword)
    (found : Internal.findCounter hashId seed (OtsKey.ofIndex layer index) message 0 limit = some choice) :
    layerRoot hashId seed layer index message (FullSign.Native.layerSignature seed secret (OtsKey.ofIndex layer index) choice) =
      some (treeRoot hashId seed (prf hashId seed secret) layer (OtsKey.ofIndex layer index).tree) := by
  rcases choice with ⟨counter,code⟩
  have hl := otsLeaf_findCounter hashId seed (prf hashId seed secret) (OtsKey.ofIndex layer index) message 0 limit counter code found
  have hb : (OtsKey.ofIndex layer index).leaf < 2^layer.height := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hp := xmss_fold_path hashId seed (prf hashId seed secret) layer (OtsKey.ofIndex layer index).tree
    (OtsKey.ofIndex layer index).leaf hb
  unfold layerRoot FullSign.Native.layerSignature
  simp only [Bind.bind,Pure.pure,hl]
  exact congrArg some hp

/-- Typed signature assembled by the three successful bounded counter searches. -/
def signingSignature (seed : PkSeed) (secret : Seed) (index : Nat) (rho : Randomizer)
    (openings : Vector TreeOpening Constants.FORS_TREES)
    (bottom middle top : UInt32 × Codeword) : Signature :=
  ⟨rho,openings,FullSign.Native.layerSignature seed secret (OtsKey.ofIndex .bottom index) bottom,
    FullSign.Native.layerSignature seed secret (OtsKey.ofIndex .middle index) middle,
    FullSign.Native.layerSignature seed secret (OtsKey.ofIndex .top index) top⟩

theorem lower_next_bottom (seed : PkSeed) (secret : Seed) (index : Nat) (message : Digest) :
    FullSign.Native.nextMessage seed secret (OtsKey.ofIndex .bottom index) message =
      treeRoot hashId seed (prf hashId seed secret) .bottom (OtsKey.ofIndex .bottom index).tree := by
  unfold FullSign.Native.nextMessage
  rfl

theorem lower_next_middle (seed : PkSeed) (secret : Seed) (index : Nat) (message : Digest) :
    FullSign.Native.nextMessage seed secret (OtsKey.ofIndex .middle index) message =
      treeRoot hashId seed (prf hashId seed secret) .middle (OtsKey.ofIndex .middle index).tree := by
  unfold FullSign.Native.nextMessage
  rfl

/-- Every combination of the signer's three successful searches verifies under its top-tree public key. -/
theorem signing_signature_verifies (seed : PkSeed) (secret : Seed) (message : Message) (rho : Randomizer)
    (digest : MessageDigest) (index : Nat) (limit : Nat)
    (hdigest : hMsg hashId rho seed (treeRoot hashId seed (prf hashId seed secret) .top 0) message = digest)
    (hindex : index = digestIndex digest) (bottom middle top : UInt32 × Codeword)
    (hbottom : Internal.findCounter hashId seed (OtsKey.ofIndex .bottom index)
      (forsSign hashId seed (prf hashId seed secret) index (digestLeaves digest)).2 0 limit = some bottom)
    (hmiddle : Internal.findCounter hashId seed (OtsKey.ofIndex .middle index)
      (treeRoot hashId seed (prf hashId seed secret) .bottom (OtsKey.ofIndex .bottom index).tree) 0 limit = some middle)
    (htop : Internal.findCounter hashId seed (OtsKey.ofIndex .top index)
      (treeRoot hashId seed (prf hashId seed secret) .middle (OtsKey.ofIndex .middle index).tree) 0 limit = some top) :
    verifyWith hashId ⟨seed,treeRoot hashId seed (prf hashId seed secret) .top 0⟩ message
      (signingSignature seed secret index rho
        (forsSign hashId seed (prf hashId seed secret) index (digestLeaves digest)).1 bottom middle top) = true := by
  have hf := fors_recover_sign hashId seed (prf hashId seed secret) index (digestLeaves digest)
  have hb := layer_signature_root seed secret .bottom index _ limit bottom hbottom
  have hm := layer_signature_root seed secret .middle index _ limit middle hmiddle
  have ht := layer_signature_root seed secret .top index _ limit top htop
  have ht0 := top_tree_zero index (by rw [hindex]; exact digest_index_bounded digest)
  rw [ht0] at ht
  unfold verifyWith
  simp only [signingSignature,Bind.bind,Pure.pure]
  simp only [hdigest,←hindex,hf,hb,hm,ht,decide_true]

end RustCrypto.CanonicalCorrectness
