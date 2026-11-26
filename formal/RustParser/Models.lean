module

public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Explicit models for the three standard-library operations absent from the
pinned Aeneas runtime. These are part of the trusted Rust standard-library
interface; this file does not verify the unsafe implementation of Rust slices. -/
namespace RustParser

def readPrefix (n : Usize) (s : Slice α) (h : n.val ≤ s.val.length) : Aeneas.Std.Array α n :=
  .from (s.val.take n.val) (by simp [List.length_take, Nat.min_eq_left h])

def readSuffix (n : Usize) (s : Slice α) : Slice α :=
  .from (s.val.drop n.val) (by
    simp only [List.length_drop]
    exact le_trans (Nat.sub_le _ _) s.property)

end RustParser

def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type _}
    (value : Option T) : Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  .ok (match value with
    | none => .Break none
    | some value => .Continue value)

def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
    (T : Type _) (value : Option Never) : Result (Option T) :=
  match value with
  | none => .ok none
  | some value => nomatch value

def core.slice.Slice.split_first_chunk {T : Type _} (n : Usize) (s : Slice T) :
    Result (Option ((Aeneas.Std.Array T n) × Slice T)) :=
  if h : n.val ≤ s.val.length then
    .ok (some (RustParser.readPrefix n s h, RustParser.readSuffix n s))
  else .ok none
