module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Mathematical semantics of the external wide interfaces. Each SIMD value is
an ordered collection of 64-bit lanes. These definitions do not certify the
external wide implementation or generated machine instructions. -/
abbrev wide.u64x2_.u64x2 := Fin 2 → U64
abbrev wide.u64x4_.u64x4 := Fin 4 → U64

namespace wide.u64x2_.u64x2

def Insts.CoreOpsBitBitOrAssignu64x2.bitor_assign (a b : wide.u64x2_.u64x2) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => a i ||| b i)

def Insts.CoreOpsBitBitXorAssignu64x2.bitxor_assign (a b : wide.u64x2_.u64x2) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => a i ^^^ b i)

def Insts.CoreOpsBitBitAndu64x2u64x2.bitand (a b : wide.u64x2_.u64x2) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => a i &&& b i)

def Insts.CoreOpsBitBitOru64x2u64x2.bitor (a b : wide.u64x2_.u64x2) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => a i ||| b i)

def Insts.CoreOpsBitBitXoru64x2u64x2.bitxor (a b : wide.u64x2_.u64x2) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => a i ^^^ b i)

def Insts.CoreOpsBitNotu64x2.not (a : wide.u64x2_.u64x2) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => ~~~(a i))

def Insts.CoreOpsBitShlU32u64x2.shl (a : wide.u64x2_.u64x2) (n : U32) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => ⟨(a i).bv.shiftLeft n.val⟩)

def Insts.CoreOpsBitShrU32u64x2.shr (a : wide.u64x2_.u64x2) (n : U32) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => ⟨(a i).bv.ushiftRight n.val⟩)

def new (a : Aeneas.Std.Array U64 2#usize) : Result wide.u64x2_.u64x2 :=
  .ok (fun i => a.val[i.val]'(by have := a.property; have := i.isLt; simp_all))

def to_array (a : wide.u64x2_.u64x2) : Result (Aeneas.Std.Array U64 2#usize) :=
  .ok (Aeneas.Std.Array.from (List.ofFn a) (by simp))

end wide.u64x2_.u64x2

namespace wide.u64x4_.u64x4

def Insts.CoreOpsBitBitOrAssignu64x4.bitor_assign (a b : wide.u64x4_.u64x4) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => a i ||| b i)

def Insts.CoreOpsBitBitXorAssignu64x4.bitxor_assign (a b : wide.u64x4_.u64x4) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => a i ^^^ b i)

def Insts.CoreOpsBitBitAndu64x4u64x4.bitand (a b : wide.u64x4_.u64x4) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => a i &&& b i)

def Insts.CoreOpsBitBitOru64x4u64x4.bitor (a b : wide.u64x4_.u64x4) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => a i ||| b i)

def Insts.CoreOpsBitBitXoru64x4u64x4.bitxor (a b : wide.u64x4_.u64x4) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => a i ^^^ b i)

def Insts.CoreOpsBitNotu64x4.not (a : wide.u64x4_.u64x4) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => ~~~(a i))

def Insts.CoreOpsBitShlU32u64x4.shl (a : wide.u64x4_.u64x4) (n : U32) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => ⟨(a i).bv.shiftLeft n.val⟩)

def Insts.CoreOpsBitShrU32u64x4.shr (a : wide.u64x4_.u64x4) (n : U32) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => ⟨(a i).bv.ushiftRight n.val⟩)

def new (a : Aeneas.Std.Array U64 4#usize) : Result wide.u64x4_.u64x4 :=
  .ok (fun i => a.val[i.val]'(by have := a.property; have := i.isLt; simp_all))

def to_array (a : wide.u64x4_.u64x4) : Result (Aeneas.Std.Array U64 4#usize) :=
  .ok (Aeneas.Std.Array.from (List.ofFn a) (by simp))

end wide.u64x4_.u64x4
