module
public import RustCrypto.Tree.ClimbBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsClimb
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives
open RustCrypto.WotsEthlib RustCrypto.ClimbBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem index_halves (kappa level index : Nat) (hlevel : level < 10) :
    (kappa * 2^(10-level)+index)/2 = kappa * 2^(10-(level+1))+index/2 ∧
    (kappa * 2^(10-level)+index)%2 = index%2 := by
  have he : 10-level = (10-(level+1))+1 := by omega
  have hp : kappa * 2^(10-level) = 2*(kappa * 2^(10-(level+1))) := by
    rw [he,Nat.pow_succ]
    ring
  rw [hp]
  omega

theorem climb_global_eq (nodes : List EthLib.Cryptography.Sphincs.Digest)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (level index : Nat)
    (node : EthLib.Cryptography.Sphincs.Digest) (hheight : level+nodes.length ≤ 10) :
    EthLib.Cryptography.Merkle.climb
      (keyNodeHash seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree)
      ⟨level,kappa.val*2^(10-level)+index⟩ node nodes =
    EthLib.Cryptography.Merkle.climb
      (EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId seed idx kappa)
      ⟨level,index⟩ node nodes := by
  induction nodes generalizing level index node with
  | nil => rfl
  | cons sibling rest ih =>
    have hl : level < 10 := by simp only [List.length_cons] at hheight; omega
    have hi := index_halves kappa.val level index hl
    let children := EthLib.Cryptography.Merkle.ordered ⟨level,index⟩ node sibling
    let parent := EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId seed idx kappa
      ⟨level+1,index/2⟩ children.1 children.2
    have hrec := ih (level+1) (index/2) parent (by simp only [List.length_cons] at hheight; omega)
    have hordered : EthLib.Cryptography.Merkle.ordered ⟨level,kappa.val*2^(10-level)+index⟩ node sibling = children := by
      simp only [children,EthLib.Cryptography.Merkle.ordered,EthLib.Cryptography.Merkle.Position.isLeft,hi.2]
      rfl
    have hhash : keyNodeHash seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree
        ⟨level+1,kappa.val*2^(10-(level+1))+index/2⟩ children.1 children.2 = parent := by
      unfold keyNodeHash
      rfl
    simp only [EthLib.Cryptography.Merkle.climb,EthLib.Cryptography.Merkle.Position.parent,
      hordered,hi.1,Bind.bind]
    change EthLib.Cryptography.Merkle.climb _ _ (keyNodeHash _ _ _ _ children.1 children.2) rest =
      EthLib.Cryptography.Merkle.climb _ _ parent rest
    rw [hhash]
    exact hrec

@[step] theorem climb_fors_ethlib_spec (address : Address) (reader : Slice U8) (position : U32)
    (node seed : Node) (idx : Nat) (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES)
    (leaf : Nat) (nodes : List Node) (tail : List U8) (hlen : nodes.length = 10)
    (hposition : position.val = EthLib.Cryptography.Sphincs.forsTreeIndex kappa 0 leaf)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree)
    (hreader : reader.val = nodesBytes nodes ++ tail) :
    lean_sphincs.tree.climb address reader position 10#u32 node ⦃ out =>
      out.1.map nativeNode = some (EthLib.Cryptography.Merkle.climb
        (EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx kappa)
        ⟨0,leaf⟩ (nativeNode node) (nodes.map nativeNode)) ∧
      out.2.2.val = tail ∧
      keyFrame out.2.1 seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ⦄ := by
  have hsource := climb_key_ethlib_spec address reader position 10#u32 node seed
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree nodes tail hlen hframe hreader
  have hcanonical := climb_global_eq (nodes.map nativeNode) (nativeNode seed) idx kappa 0 leaf
    (nativeNode node) (by simp only [List.length_map,hlen]; omega)
  have hp : position.val = kappa.val*2^(10-0)+leaf := hposition
  simpa only [hp,hcanonical] using hsource

end RustCrypto.ForsClimb
