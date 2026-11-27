module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/-! The pinned translator emits an explicit array length for these two trait
constructors; the runtime marks that same parameter implicit. These adapters
only restore the calling convention and preserve the runtime definitions. -/
namespace lean_sphincs

@[reducible] def core.ops.index.IndexArray {T I O : Type _} (N : Usize)
    (inst : Aeneas.Std.core.ops.index.Index (Slice T) I O) :=
  Aeneas.Std.core.ops.index.IndexArray (N := N) inst

@[reducible] def core.ops.index.IndexMutArray {T I O : Type _} (N : Usize)
    (inst : Aeneas.Std.core.ops.index.IndexMut (Slice T) I O) :=
  Aeneas.Std.core.ops.index.IndexMutArray (N := N) inst

end lean_sphincs

/- Explicit scalar remainder emitted after Charon has reconstructed its guard. -/
@[reducible] def Aeneas.Std.U32.rem (x y : U32) : Result U32 := UScalar.rem x y
