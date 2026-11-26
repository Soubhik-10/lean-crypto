module
public import RustCrypto.KeyGen
public import RustCrypto.RootBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

abbrev Nodes := Aeneas.Std.Array Node 2048#usize

def width (height : Nat) : Nat := 2^(10-height)

@[irreducible] def value (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (height index : Nat) :
    EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.node EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) .top 0 height index

theorem value_zero (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (index : Nat) :
    value seed secret 0 index = EthLib.Cryptography.Sphincs.leaves EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) .top 0 index := by
  unfold value EthLib.Cryptography.Sphincs.node EthLib.Cryptography.Merkle.node
  rfl

theorem value_succ (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (height index : Nat) :
    value seed secret (height+1) index =
      EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) .top 0 ⟨height+1,index⟩
        (value seed secret height (2*index)) (value seed secret height (2*index+1)) := by
  unfold value EthLib.Cryptography.Sphincs.node EthLib.Cryptography.Merkle.node
  rfl

def levelValid (nodes : Nodes) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (height : Nat) : Prop :=
  ∀ index < width height, nativeNode (nodes[width height+index]!) = value seed secret height index

def validThrough (nodes : Nodes) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (height : Nat) : Prop :=
  ∀ level ≤ height, levelValid nodes seed secret level

theorem width_zero : width 0 = 1024 := by decide

theorem width_top : width 10 = 1 := by decide

theorem width_bounded (height : Nat) : width height ≤ 1024 := by
  calc
    width height ≤ 2^10 := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    _ = 1024 := by decide

theorem width_positive (height : Nat) : 0 < width height := Nat.pow_pos (by decide)

theorem width_succ (height : Nat) (hheight : height < 10) : width height = 2*width (height+1) := by
  have he : 10-height = (10-(height+1))+1 := by omega
  unfold width
  rw [he,Nat.pow_succ]
  omega

theorem width_antitone (a b : Nat) (hab : a ≤ b) : width b ≤ width a := by
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem array_set_read {T : Type} [Inhabited T] {n : Usize} (nodes : Aeneas.Std.Array T n)
    (index : Usize) (item : T) (j : Nat) (hj : j < n.val) :
    (nodes.set index item)[j]! = if j = index.val then item else nodes[j]! := by
  by_cases heq : j = index.val
  · simp only [ite_eq_left heq]
    exact Aeneas.Std.Array.getElem!_Nat_set_eq nodes index j item ⟨heq.symm,by simpa using hj⟩
  · simp only [ite_eq_right heq]
    exact Aeneas.Std.Array.getElem!_Nat_set_ne nodes index j item (Ne.symm heq)

@[step] theorem top_leaves_spec : lean_sphincs.tree.TOP_LEAVES ⦃ out => out = 1024#usize ⦄ := by
  unfold lean_sphincs.tree.TOP_LEAVES
  step with KeyGen.max_tree_height_spec as ⟨height,hheight⟩
  rw [hheight]
  have hbits := System.Platform.le_numBits
  step as ⟨result,hresult⟩
  apply UScalar.eq_of_val_eq
  norm_num [Nat.shiftLeft_eq] at hresult
  have hsize : 1024 < Usize.size := by
    have hp : 2^32 ≤ 2^System.Platform.numBits := Nat.pow_le_pow_right (by decide) hbits
    norm_num1 at hp
    simpa only [Usize.size,Usize.numBits,UScalarTy.numBits] using (show 1024 < 2^System.Platform.numBits by omega)
  rw [Nat.mod_eq_of_lt hsize] at hresult
  scalar_tac

end RustCrypto.TopCache
