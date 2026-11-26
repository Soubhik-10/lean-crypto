module
public import RustCrypto.BuildRoot
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
set_option maxHeartbeats 2000000

@[irreducible] def selectedValue {α : Type} (values : Nat → α) (zero : α) (height index target : Nat) : α :=
  if target / 2^height = index then values target else zero

theorem selected_zero {α : Type} (values : Nat → α) (zero : α) (index target : Nat) :
    selectedValue values zero 0 index target = if index = target then values index else zero := by
  unfold selectedValue
  by_cases he : index = target
  · subst target
    simp
  · simp [he,Ne.symm he]

theorem selected_succ {α : Type} (values : Nat → α) (zero : α) (height index target : Nat) :
    selectedValue values zero (height+1) index target =
      if target / 2^height % 2 = 0 then selectedValue values zero height (2*index) target
      else selectedValue values zero height (2*index+1) target := by
  unfold selectedValue
  have hd : target / 2^(height+1) = (target/2^height)/2 := by
    rw [Nat.pow_succ,Nat.div_div_eq_div_mul]
  rw [hd]
  by_cases he : target/2^height % 2 = 0
  · have hl : target/2^height = 2*index ↔ (target/2^height)/2 = index := by omega
    simp only [he,reduceIte,hl]
  · have hr : target/2^height = 2*index+1 ↔ (target/2^height)/2 = index := by omega
    simp only [he,reduceIte,hr]

end RustCrypto.BuildRoot
