module
public import RustCrypto.Tree.Build.PathPatch
@[expose] public section
namespace RustCrypto.BuildRoot
set_option maxHeartbeats 2000000

theorem covered_root_iff (height target level : Nat) (htarget : target < 2^height) :
    covered height 0 target level ↔ level < height := by
  by_cases hl : level < height
  · have hle : level ≤ height := by omega
    have he : level+(height-level) = height := by omega
    have hone : 1 < 2^(height-level) := by
      have hp : 2^1 ≤ 2^(height-level) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hz : siblingIndex target level / 2^(height-level) = 0 := by
      rw [siblingIndex,Nat.xor_div_two_pow,Nat.div_div_eq_div_mul,← Nat.pow_add,he,
        Nat.div_eq_of_lt htarget,Nat.div_eq_of_lt hone]
      rfl
    simp only [covered,hle,hz,true_and,hl]
  · by_cases he : level = height
    · subst level
      rw [covered_top]
      have hs : siblingIndex target height = 1 := by
        rw [siblingIndex,Nat.div_eq_of_lt htarget]
        rfl
      simp [hs]
    · have hle : ¬level ≤ height := by omega
      simp only [covered,hle,false_and,hl]

theorem patch_root (values : Nat → α) (height target : Nat) (original : List α) (htarget : target < 2^height) :
    patch values height 0 target original = original.mapIdx (fun level old => if level < height then values level else old) := by
  simp only [patch,covered_root_iff height target _ htarget]

theorem patch_full_path (values : Nat → α) (height target : Nat) (original : List α)
    (htarget : target < 2^height) (hlen : original.length = height) :
    patch values height 0 target original = List.ofFn (fun level : Fin height => values level.val) := by
  rw [patch_root values height target original htarget]
  apply List.ext_getElem
  · simpa using hlen
  · intro level hi _
    have hl : level < height := by simpa [hlen] using hi
    simp only [List.getElem_mapIdx,ite_eq_left hl,List.getElem_ofFn]

end RustCrypto.BuildRoot
