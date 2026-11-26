module
public import RustCrypto.BuildFinish
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem set_opt_none (values : List α) (index : Nat) : values.set_opt index none = values := by
  induction values generalizing index with
  | nil => simp
  | cons a rest ih => cases index <;> simp [ih]

theorem set_opt_some (values : List α) (index : Nat) (value : α) :
    values.set_opt index (some value) = values.set index value := by
  induction values generalizing index with
  | nil => simp
  | cons a rest ih => cases index <;> simp [ih]

@[step] theorem finish_path_spec (address : Address) (path : Slice Node) (height index target : U32)
    (node selected : Node) (hheight : height.val < 32) :
    finish address path height index target node selected ⦃ out =>
      out.2.2.val = if index.val = (target.val / 2^height.val) ^^^ 1 then path.val.set height.val node else path.val ⦄ := by
  unfold finish
  step as ⟨shifted,hshifted⟩
  step as ⟨sibling,hsibling⟩
  have hone : (1#u32).val = 1 := rfl
  have hs : sibling.val = (target.val/2^height.val) ^^^ 1 := by
    rw [hsibling,UScalar.val_xor,hone,hshifted,Nat.shiftRight_eq_div_pow]
  have heq : index = sibling ↔ index.val = (target.val/2^height.val) ^^^ 1 := by
    constructor
    · intro h
      have hv := congrArg UScalar.val h
      simpa only [hs] using hv
    · intro h
      apply UScalar.eq_of_val_eq
      rw [hs]
      exact h
  by_cases hmatch : index = sibling
  · simp only [ite_eq_left hmatch,ite_eq_left (heq.mp hmatch)]
    step as ⟨level,hlevel⟩
    have hl : level.val = height.val := by scalar_tac
    simp only [Aeneas.Std.uncurry,core.slice.Slice.get_mut,core.slice.index.Usize.get_mut,Aeneas.Std.bind_ok]
    cases hcurrent : path[level]? with
    | none =>
      have hbound : path.val.length ≤ level.val := by simpa only [Slice.getElem?_Usize_eq,List.getElem?_eq_none_iff] using hcurrent
      simp only [WP.spec_ok,Slice.set_opt_val_eq,set_opt_none]
      rw [List.set_eq_of_length_le (by omega)]
    | some value =>
      simp only [WP.spec_ok,Slice.set_opt_val_eq,set_opt_some,hl]
  · have hnomatch : index.val ≠ (target.val/2^height.val) ^^^ 1 := fun h => hmatch (heq.mpr h)
    simp only [ite_eq_right hmatch,ite_eq_right hnomatch,WP.spec_ok]

end RustCrypto.BuildRoot
