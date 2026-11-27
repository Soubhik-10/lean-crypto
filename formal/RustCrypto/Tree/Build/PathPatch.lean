module
public import RustCrypto.Tree.Build.Coverage
@[expose] public section
namespace RustCrypto.BuildRoot
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

instance coveredDecidable (height index target level : Nat) : Decidable (covered height index target level) := by
  unfold covered
  infer_instance

def patch (values : Nat → α) (height index target : Nat) (original : List α) : List α :=
  original.mapIdx fun level old => if covered height index target level then values level else old

@[simp] theorem patch_length (values : Nat → α) (height index target : Nat) (original : List α) :
    (patch values height index target original).length = original.length := by simp [patch]

theorem patch_zero (values : Nat → α) (index target : Nat) (original : List α) :
    patch values 0 index target original =
      if index = siblingIndex target 0 then original.set 0 (values 0) else original := by
  by_cases hmatch : index = siblingIndex target 0
  · rw [ite_eq_left hmatch]
    apply List.ext_getElem
    · simp
    · intro level _ _
      by_cases hlevel : level = 0
      · subst level
        simp [patch,covered_zero,hmatch]
      · simp [patch,covered_zero,hlevel,Ne.symm hlevel]
  · rw [ite_eq_right hmatch]
    apply List.ext_getElem
    · simp
    · intro level _ _
      simp [patch,covered_zero,Ne.symm hmatch]

theorem patch_succ (values : Nat → α) (height index target : Nat) (original : List α) :
    patch values (height+1) index target original =
      let children := patch values height (2*index+1) target (patch values height (2*index) target original)
      if index = siblingIndex target (height+1) then children.set (height+1) (values (height+1)) else children := by
  dsimp only
  by_cases hmatch : index = siblingIndex target (height+1)
  · rw [ite_eq_left hmatch]
    apply List.ext_getElem
    · simp
    · intro level _ _
      by_cases hlevel : level = height+1
      · subst level
        simp [patch,covered,hmatch]
      · simp only [patch,List.getElem_mapIdx,List.getElem_set,Ne.symm hlevel,reduceIte,covered_succ,hlevel,false_and,false_or]
        by_cases hleft : covered height (2*index) target level <;>
          by_cases hright : covered height (2*index+1) target level <;> simp [hleft,hright]
  · rw [ite_eq_right hmatch]
    apply List.ext_getElem
    · simp
    · intro level _ _
      by_cases hlevel : level = height+1
      · subst level
        simp [patch,covered,hmatch,Eq.comm]
      · simp only [patch,List.getElem_mapIdx,covered_succ,hlevel,false_and,false_or]
        by_cases hleft : covered height (2*index) target level <;>
          by_cases hright : covered height (2*index+1) target level <;> simp [hleft,hright]

end RustCrypto.BuildRoot
