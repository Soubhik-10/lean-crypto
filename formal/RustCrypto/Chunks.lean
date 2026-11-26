module
public import Aeneas
public import RustParser.Models
@[expose] public section
open Aeneas Aeneas.Std Result

namespace RustCrypto

def chunk {T : Type _} (n : Usize) (s : Slice T) (i : Fin (s.val.length / n.val)) :
    Aeneas.Std.Array T n :=
  Aeneas.Std.Array.from ((s.val.drop (i.val * n.val)).take n.val) (by
    have h := Nat.mul_le_mul_right n.val (show i.val + 1 ≤ s.val.length / n.val by omega)
    have hd := Nat.div_mul_le_self s.val.length n.val
    simp only [Nat.add_mul, Nat.one_mul] at h
    simp only [List.length_take, List.length_drop]
    omega)

def chunks {T : Type _} (n : Usize) (s : Slice T) :
    Slice (Aeneas.Std.Array T n) :=
  Slice.from (List.ofFn (chunk n s)) (by
    simp only [List.length_ofFn]
    exact le_trans (Nat.div_le_self _ _) s.property)

end RustCrypto

def core.slice.Slice.as_chunks {T : Type _} (n : Usize) (s : Slice T) :
    Result (Slice (Aeneas.Std.Array T n) × Slice T) :=
  if n.val = 0 then .fail .panic
  else .ok (RustCrypto.chunks n s,
    RustParser.readSuffix (Usize.ofNatCore ((s.val.length / n.val) * n.val)
      (by have h := Nat.div_mul_le_self s.val.length n.val; scalar_tac)) s)

def core.panicking.panic_const.panic_const_rem_by_zero : Result Never := .fail .panic
