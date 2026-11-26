module
public import RustCrypto.FinishPath
@[expose] public section
namespace RustCrypto.BuildRoot
set_option maxHeartbeats 2000000

def siblingIndex (target level : Nat) : Nat := (target/2^level) ^^^ 1

def covered (height index target level : Nat) : Prop :=
  level ≤ height ∧ siblingIndex target level / 2^(height-level) = index

theorem covered_top (height index target : Nat) :
    covered height index target height ↔ siblingIndex target height = index := by
  simp [covered]

theorem covered_zero (index target level : Nat) :
    covered 0 index target level ↔ level = 0 ∧ siblingIndex target 0 = index := by
  cases level <;> simp [covered]

theorem covered_succ (height index target level : Nat) :
    covered (height+1) index target level ↔
      (level = height+1 ∧ siblingIndex target level = index) ∨
      covered height (2*index) target level ∨ covered height (2*index+1) target level := by
  by_cases he : level = height+1
  · subst level
    simp [covered]
  · by_cases hl : level ≤ height
    · have hp : 2^(height+1-level) = 2^(height-level)*2 := by
        have hn : height+1-level = (height-level)+1 := by omega
        rw [hn,Nat.pow_succ]
      have hd : siblingIndex target level / 2^(height+1-level) =
          (siblingIndex target level / 2^(height-level))/2 := by
        rw [hp,Nat.div_div_eq_div_mul]
      have hlp : level ≤ height+1 := by omega
      simp only [covered,hl,hlp,true_and,he,false_and,false_or,hd]
      omega
    · have hlp : ¬level ≤ height+1 := by omega
      simp only [covered,hl,hlp,false_and,he,false_or]

theorem covered_children_disjoint (height index target level : Nat) :
    ¬ (covered height (2*index) target level ∧ covered height (2*index+1) target level) := by
  unfold covered
  omega

end RustCrypto.BuildRoot
