module
public import RustCrypto.MerklePath
@[expose] public section
namespace RustCrypto.MerklePath
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem build_zero (hash : EthLib.Cryptography.Merkle.Position → α → α → Id α) (leaves : Nat → Id α) (index : Nat) :
    EthLib.Cryptography.Merkle.build hash leaves ⟨0,index⟩ = .leaf (leaves index) := by rfl

theorem build_succ (hash : EthLib.Cryptography.Merkle.Position → α → α → Id α) (leaves : Nat → Id α) (height index : Nat) :
    EthLib.Cryptography.Merkle.build hash leaves ⟨height+1,index⟩ =
      let left := EthLib.Cryptography.Merkle.build hash leaves ⟨height,2*index⟩
      let right := EthLib.Cryptography.Merkle.build hash leaves ⟨height,2*index+1⟩
      .node (hash ⟨height+1,index⟩ left.value right.value) left right := by rfl

theorem build_value (hash : EthLib.Cryptography.Merkle.Position → α → α → Id α) (leaves : Nat → Id α) (height index : Nat) :
    (EthLib.Cryptography.Merkle.build hash leaves ⟨height,index⟩).value =
      EthLib.Cryptography.Merkle.node.go hash leaves height index := by
  induction height generalizing index with
  | zero => rw [build_zero]; rfl
  | succ height ih =>
    rw [build_succ]
    change hash ⟨height+1,index⟩
      (EthLib.Cryptography.Merkle.build hash leaves ⟨height,2*index⟩).value
      (EthLib.Cryptography.Merkle.build hash leaves ⟨height,2*index+1⟩).value = _
    rw [ih,ih]
    rfl

theorem xor_even (index : Nat) : (2*index) ^^^ 1 = 2*index+1 := by
  have hd : ((2*index) ^^^ 1)/2 = index := by rw [Nat.xor_div_two]; simp
  have hm : ((2*index) ^^^ 1)%2 = 1 := by rw [Nat.xor_mod_two_eq_one]; omega
  omega

theorem xor_odd (index : Nat) : (2*index+1) ^^^ 1 = 2*index := by
  have hd : ((2*index+1) ^^^ 1)/2 = index := by rw [Nat.xor_div_two]; simp; omega
  have hm : ¬ ((2*index+1) ^^^ 1)%2 = 1 := by rw [Nat.xor_mod_two_eq_one]; omega
  omega

theorem build_path_list (hash : EthLib.Cryptography.Merkle.Position → α → α → Id α) (leaves : Nat → Id α)
    (height index target : Nat) (hindex : target/2^height = index) :
    ((EthLib.Cryptography.Merkle.build hash leaves ⟨height,index⟩).path height target).toList =
      List.ofFn (fun level : Fin height => EthLib.Cryptography.Merkle.node.go hash leaves
        level.val ((target/2^level.val) ^^^ 1)) := by
  induction height generalizing index with
  | zero => rfl
  | succ height ih =>
    have hd : target/2^(height+1) = (target/2^height)/2 := by rw [Nat.pow_succ,Nat.div_div_eq_div_mul]
    rw [hd] at hindex
    rw [build_succ]
    dsimp only
    by_cases he : target/2^height%2 = 0
    · have hi : target/2^height = 2*index := by omega
      simp only [EthLib.Cryptography.Merkle.Built.path,ite_eq_left he,Vector.toList_push]
      rw [ih (2*index) hi,build_value,List.ofFn_succ_last]
      simp only [Fin.val_castSucc,Fin.val_last,hi,xor_even]
    · have hi : target/2^height = 2*index+1 := by omega
      simp only [EthLib.Cryptography.Merkle.Built.path,ite_eq_right he,Vector.toList_push]
      rw [ih (2*index+1) hi,build_value,List.ofFn_succ_last]
      simp only [Fin.val_castSucc,Fin.val_last,hi,xor_odd]

end RustCrypto.MerklePath
