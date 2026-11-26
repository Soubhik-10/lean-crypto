module
public import RustCrypto.MerkleBuilt
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
open EthLib.Cryptography.Merkle

theorem node_parent {α : Type} (hash : Position → α → α → Id α) (leaves : Nat → Id α)
    (level index : Nat) :
    hash (Position.parent ⟨level,index⟩)
      (ordered ⟨level,index⟩ (node hash leaves ⟨level,index⟩) (node hash leaves (Position.sibling ⟨level,index⟩))).1
      (ordered ⟨level,index⟩ (node hash leaves ⟨level,index⟩) (node hash leaves (Position.sibling ⟨level,index⟩))).2 =
      node hash leaves (Position.parent ⟨level,index⟩) := by
  by_cases he : index % 2 = 0
  · have hi : index = 2*(index/2) := by omega
    have hx : index ^^^ 1 = 2*(index/2)+1 := by
      calc
        index ^^^ 1 = (2*(index/2)) ^^^ 1 := congrArg (fun n => n ^^^ 1) hi
        _ = _ := RustCrypto.MerklePath.xor_even _
    simp only [ordered,Position.isLeft,he,decide_true,ite_true,Position.parent,Position.sibling,node,node.go]
    rw [hx]
    conv_lhs => arg 2; rw [hi]
    rfl
  · have hi : index = 2*(index/2)+1 := by omega
    have hx : index ^^^ 1 = 2*(index/2) := by
      calc
        index ^^^ 1 = (2*(index/2)+1) ^^^ 1 := congrArg (fun n => n ^^^ 1) hi
        _ = _ := RustCrypto.MerklePath.xor_odd _
    simp only [ordered,Position.isLeft,he,decide_false,Bool.false_eq_true,ite_false,Position.parent,Position.sibling,node,node.go]
    rw [hx]
    conv_lhs => arg 3; rw [hi]
    rfl

theorem climb_siblings {α : Type} (hash : Position → α → α → Id α) (leaves : Nat → Id α)
    (height level index : Nat) :
    climb hash ⟨level,index⟩ (node hash leaves ⟨level,index⟩)
      (siblings hash leaves ⟨level,index⟩ height).toList =
      node hash leaves ⟨level+height,index/2^height⟩ := by
  induction height generalizing level index with
  | zero =>
    change node hash leaves ⟨level,index⟩ = node hash leaves ⟨level+0,index/2^0⟩
    simp only [Nat.add_zero,Nat.pow_zero,Nat.div_one]
  | succ height ih =>
    simp only [siblings,Bind.bind,Pure.pure,Vector.toList_cast,Vector.toList_append]
    change climb hash ⟨level,index⟩ (node hash leaves ⟨level,index⟩)
      ((node hash leaves (Position.sibling ⟨level,index⟩)) ::
        (siblings hash leaves (Position.parent ⟨level,index⟩) height).toList) = _
    rw [climb]
    change climb hash (Position.parent ⟨level,index⟩)
      (hash (Position.parent ⟨level,index⟩)
        (ordered ⟨level,index⟩ (node hash leaves ⟨level,index⟩) (node hash leaves (Position.sibling ⟨level,index⟩))).1
        (ordered ⟨level,index⟩ (node hash leaves ⟨level,index⟩) (node hash leaves (Position.sibling ⟨level,index⟩))).2)
      (siblings hash leaves (Position.parent ⟨level,index⟩) height).toList = _
    rw [node_parent hash leaves level index]
    rw [show Position.parent ⟨level,index⟩ = ⟨level+1,index/2⟩ from rfl,ih]
    congr 1
    apply Position.ext
    · dsimp only; omega
    · dsimp only
      rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (2^height) 2]

theorem climb_path {α : Type} (hash : Position → α → α → Id α) (leaves : Nat → Id α)
    (height index : Nat) (hindex : index < 2^height) :
    climb hash ⟨0,index⟩ (leaves index) (path hash leaves height index).toList =
      root hash leaves height := by
  have h := climb_siblings hash leaves height 0 index
  simpa only [path,node,node.go,Nat.zero_add,Nat.div_eq_of_lt hindex,root] using h

end RustCrypto.CanonicalCorrectness
