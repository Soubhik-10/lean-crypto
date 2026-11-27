module
public import RustCrypto.Tree.Cache.Model
public import RustCrypto.Tree.MerkleBuilt
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

/-- Toggling bit zero commutes with adding any even block offset. -/
theorem xor_one_even_add (block index : Nat) : (2*block+index) ^^^ 1 = 2*block+(index ^^^ 1) := by
  by_cases he : index%2 = 0
  · have hi : index = 2*(index/2) := by omega
    rw [hi]
    have hs : 2*block+2*(index/2) = 2*(block+index/2) := by omega
    rw [hs,RustCrypto.MerklePath.xor_even,RustCrypto.MerklePath.xor_even]
    omega
  · have hi : index = 2*(index/2)+1 := by omega
    rw [hi]
    have hs : 2*block+(2*(index/2)+1) = 2*(block+index/2)+1 := by omega
    rw [hs,RustCrypto.MerklePath.xor_odd,RustCrypto.MerklePath.xor_odd]
    omega

theorem sibling_bound (leaf level : Nat) (hleaf : leaf < 1024) (hlevel : level < 10) :
    (leaf/2^level) ^^^ 1 < width level := by
  have he : level+(10-level) = 10 := by omega
  have hone : 1 < 2^(10-level) := by
    have hp : 2^1 ≤ 2^(10-level) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hz : ((leaf/2^level) ^^^ 1) / 2^(10-level) = 0 := by
    rw [Nat.xor_div_two_pow,Nat.div_div_eq_div_mul,←Nat.pow_add,he]
    rw [show leaf/2^10 = 0 from Nat.div_eq_of_lt hleaf,Nat.div_eq_of_lt hone]
    rfl
  have hp : 0 < 2^(10-level) := Nat.pow_pos (by decide)
  change (leaf/2^level) ^^^ 1 < 2^(10-level)
  have hm := Nat.mod_lt ((leaf/2^level) ^^^ 1) hp
  have hd := Nat.mod_add_div ((leaf/2^level) ^^^ 1) (2^(10-level))
  simp only [hz,Nat.mul_zero,Nat.add_zero] at hd
  omega

/-- Source heap indexing selects exactly the sibling node at the requested level. -/
theorem heap_path_index (leaf level : Nat) (hlevel : level < 10) :
    ((1024+leaf)/2^level) ^^^ 1 = width level+((leaf/2^level) ^^^ 1) := by
  have hpow : 1024 = width level*2^level := by
    have he : 10-level+level = 10 := by omega
    unfold width
    rw [←Nat.pow_add,he]
  have hpos : 0 < 2^level := Nat.pow_pos (by decide)
  have hdiv : (1024+leaf)/2^level = width level+leaf/2^level := by
    rw [hpow,Nat.mul_comm (width level) (2^level),Nat.mul_add_div hpos]
  have heven : width level = 2*width (level+1) := width_succ level hlevel
  rw [hdiv,heven,xor_one_even_add]

end RustCrypto.TopCache
