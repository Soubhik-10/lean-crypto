module
public import RustCrypto.Tree.Build.RootCoverage
@[expose] public section
namespace RustCrypto.MerklePath
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem siblings_list (hash : EthLib.Cryptography.Merkle.Position → α → α → Id α) (leaves : Nat → Id α)
    (height start index : Nat) :
    (EthLib.Cryptography.Merkle.siblings hash leaves ⟨start,index⟩ height).toList =
      List.ofFn (fun level : Fin height => EthLib.Cryptography.Merkle.node.go hash leaves
        (start+level.val) ((index/2^level.val) ^^^ 1)) := by
  induction height generalizing start index with
  | zero => rfl
  | succ height ih =>
    simp [Vector.toList_cast,Vector.toList_append,EthLib.Cryptography.Merkle.siblings,Bind.bind,Pure.pure,ih,
      EthLib.Cryptography.Merkle.Position.parent,EthLib.Cryptography.Merkle.Position.sibling,
      EthLib.Cryptography.Merkle.node,List.ofFn_succ,Nat.pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm]
    funext level
    congr 1
    omega

end RustCrypto.MerklePath
