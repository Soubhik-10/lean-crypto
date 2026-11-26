module
public import RustCrypto.ForsClimb
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain
set_option maxHeartbeats 2000000

def finish (address : Address) (path : Slice Node) (height index target : U32) (node selected : Node) :
    Result ((Node × Node) × Address × Slice Node) := do
  let shifted ← target >>> height
  let sibling ← lift (shifted ^^^ 1#u32)
  if index = sibling then
    let level ← lift (UScalar.cast .Usize height)
    let (current,back) ← core.slice.Slice.get_mut (core.slice.index.SliceIndexUsizeSlice Node) path level
    match current with
    | none => ok ((node,selected),address,back none)
    | some _ => ok ((node,selected),address,back (some node))
  else ok ((node,selected),address,path)

@[step] theorem finish_spec (address : Address) (path : Slice Node) (height index target : U32)
    (node selected : Node) (hheight : height.val < 32) :
    finish address path height index target node selected ⦃ out => out.1 = (node,selected) ∧ out.2.1 = address ⦄ := by
  unfold finish
  step as ⟨shifted,hshifted⟩
  step as ⟨sibling,hsibling⟩
  by_cases hmatch : index = sibling
  · rw [ite_eq_left hmatch]
    step as ⟨level,hlevel⟩
    simp only [Aeneas.Std.uncurry,core.slice.Slice.get_mut,
      core.slice.index.Usize.get_mut,Aeneas.Std.bind_ok]
    cases path[level]? <;> simp [WP.spec_ok]
  · rw [ite_eq_right hmatch]
    simp only [WP.spec_ok]
    trivial

end RustCrypto.BuildRoot
