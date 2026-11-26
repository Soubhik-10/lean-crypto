module
public import LeanSphincs.Types
public import RustCrypto.Compat
public import RustCrypto.Chunks
public import RustParser.Models
public import EthLib.Cryptography.Hash.Keccak
public import Init.Data.Vector.Lemmas
@[expose] public section
open Aeneas Aeneas.Std Result
open lean_sphincs

/-! Concrete standard-library and Alloy interface semantics. Observable formatting
uses the explicit standard-library model documented in formal/Runtime. -/
def core.bool.Bool.then_some {T : Type _} (b : Bool) (x : T) : Result (Option T) :=
  .ok (if b then some x else none)

def Shared0T.Insts.CoreConvertAsRef.as_ref {T U : Type _}
    (inst : core.convert.AsRef T U) (x : T) : Result U := inst.as_ref x

def Slice.Insts.CoreConvertAsRefSlice.as_ref {T : Type _} (x : Slice T) :
    Result (Slice T) := .ok x

def Shared0T.Insts.CoreFmtDisplay.fmt {T : Type _} (inst : core.fmt.Display T)
    (x : T) (f : core.fmt.Formatter) := inst.fmt x f

def core.slice.Slice.first_chunk {T : Type _} (n : Usize) (s : Slice T) :
    Result (Option (Aeneas.Std.Array T n)) :=
  if h : n.val ≤ s.val.length then .ok (some (RustParser.readPrefix n s h))
  else .ok none

def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreCloneClone.clone {N : Usize}
    (x : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes N) := Result.ok x

def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndex.index
    {I O : Type _} {N : Usize} (inst : core.ops.index.Index (Aeneas.Std.Array U8 N) I O)
    (x : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes N) (i : I) := inst.index x i

def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndexMut.index_mut
    {I O : Type _} {N : Usize} (inst : core.ops.index.IndexMut (Aeneas.Std.Array U8 N) I O)
    (x : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes N) (i : I) := inst.index_mut x i

def alloy_primitives.bits.fixed.FixedBytes.Insts.CoreConvertAsRefSliceU8.as_ref
    {N : Usize} (x : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes N) :=
  Result.ok (Aeneas.Std.Array.to_slice x)

def alloy_primitives.bits.fixed.FixedBytes.ZERO (N : Usize) :
    Result (lean_sphincs.alloy_primitives.bits.fixed.FixedBytes N) :=
  .ok (Aeneas.Std.Array.repeat N 0#u8)

def alloy_primitives.bits.fixed.FixedBytes.new {N : Usize} (x : Aeneas.Std.Array U8 N) :=
  Result.ok x

def alloy_primitives.bits.fixed.FixedBytes.as_slice {N : Usize}
    (x : lean_sphincs.alloy_primitives.bits.fixed.FixedBytes N) :=
  Result.ok (Aeneas.Std.Array.to_slice x)

namespace RustCrypto

def bytes (xs : List U8) : ByteArray :=
  ⟨(xs.map fun x => UInt8.ofNat x.val).toArray⟩

def digest (xs : List U8) : Aeneas.Std.Array U8 32#usize :=
  Aeneas.Std.Array.from
    ((EthLib.Cryptography.Hash.Keccak.keccak256 (bytes xs)).toList.map fun x =>
      (⟨x.toNat, by have := x.toNat_lt; scalar_tac⟩ : U8)) (by simp [Vector.toList, EthLib.Cryptography.Hash.Keccak.DIGEST_LEN_256])

end RustCrypto

def alloy_primitives.utils.keccak256_uncached {T : Type _}
    (inst : core.convert.AsRef T (Slice U8)) (x : T) := do
  let data ← inst.as_ref x
  Result.ok (RustCrypto.digest data.val)

def alloy_primitives.utils.Keccak256.new : Result alloy_primitives.utils.Keccak256 := .ok []

def alloy_primitives.utils.Keccak256.update {T : Type _}
    (inst : core.convert.AsRef T (Slice U8))
    (state : alloy_primitives.utils.Keccak256) (x : T) := do
  let data ← inst.as_ref x
  Result.ok (state ++ data.val)

def alloy_primitives.utils.Keccak256.finalize (state : alloy_primitives.utils.Keccak256) :=
  Result.ok (RustCrypto.digest state)
