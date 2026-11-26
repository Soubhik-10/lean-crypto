module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.Array.Array
public import Aeneas.Std.StringDef
public import Aeneas.Std.Core.FmtModel
public section

namespace Aeneas.Std

@[reducible, expose, rust_type "core::fmt::Error"]
def core.fmt.Error := Unit

@[expose, rust_type "core::fmt::Formatter"]
def core.fmt.Formatter := RustFmt.Formatter

@[rust_trait "core::fmt::Debug"]
structure core.fmt.Debug (T : Type u) where
  fmt : T → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

-- TODO: move?
@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap"]
def core.result.Result.unwrap {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result T :=
  match e with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

@[step]
theorem core.result.Result.unwrap.step_spec
    {T E : Type _} (inst : core.fmt.Debug E)
    (r : core.result.Result T E)
    (h : ∃ v, r = core.result.Result.Ok v) :
    core.result.Result.unwrap inst r
    ⦃ (result : T) => r = core.result.Result.Ok result ⦄ := by
  match r, h with
  | .Ok v, ⟨_, rfl⟩ =>
    simp [core.result.Result.unwrap, WP.spec_ok]

-- TODO: add pattern once we support partial monomorphization
def core.result.Result.unwrap.mut {T E : Type _}
  (_ : core.fmt.Debug E) (e : core.result.Result T E) : Std.Result (T × (T → core.result.Result T E)) :=
  match e with
  | .Ok x => .ok (x, fun x => .Ok x)
  | .Err _ => .fail .panic


@[expose, rust_type "core::fmt::Arguments"]
def core.fmt.Arguments := RustFmt.Arguments

@[expose, rust_type "core::fmt::rt::Argument"]
def core.fmt.rt.Argument := RustFmt.Argument

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::from_str"]
def core.fmt.Arguments.from_str (text : Str) : Result core.fmt.Arguments := .ok { static := some text.val }

@[expose, rust_fun "core::fmt::{core::fmt::Arguments<'a>}::new"]
def core.fmt.Arguments.new {N : Std.Usize} {M : Std.Usize}
  (template : Std.Array Std.U8 N) (values : Std.Array core.fmt.rt.Argument M) : Result core.fmt.Arguments :=
  .ok { template := template.val, values := values.val }

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_debug"]
def core.fmt.rt.Argument.new_debug
  {T : Type _} (DebugInst : core.fmt.Debug T) (value : T) : Result core.fmt.rt.Argument :=
  .ok { format := DebugInst.fmt value }

@[rust_trait "core::fmt::Display"]
structure core.fmt.Display (Self : Type _) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[rust_trait "core::fmt::LowerHex"]
structure core.fmt.LowerHex (Self : Type _) where
  fmt : Self → core.fmt.Formatter → Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_lower_hex"]
def core.fmt.rt.Argument.new_lower_hex
  {T : Type _} (LowerHexInst : core.fmt.LowerHex T) (value : T) :
  Result core.fmt.rt.Argument :=
  .ok { format := LowerHexInst.fmt value }

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_str"]
def core.fmt.Formatter.write_str (fmt : core.fmt.Formatter) (text : Str) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.writeBytes fmt text.val

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::write_fmt"]
def core.fmt.Formatter.write_fmt
  (fmt : core.fmt.Formatter) (args : core.fmt.Arguments) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.writeArguments fmt args

@[expose, rust_fun "core::fmt::{core::fmt::Debug<&'0 @T>}::fmt"]
def core.fmt.DebugShared.fmt {T : Type _} (DebugInst : core.fmt.Debug T) (x : T)
  (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  DebugInst.fmt x fmt

@[expose, rust_fun "core::fmt::{core::fmt::Debug<bool>}::fmt"]
def core.fmt.DebugBool.fmt (value : Bool) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.padAscii fmt (RustFmt.ascii (if value then "true" else "false"))

@[expose, rust_fun "core::fmt::{core::fmt::Debug<()>}::fmt"]
def core.fmt.DebugUnit.fmt (_ : Unit) (fmt : core.fmt.Formatter) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.padAscii fmt (RustFmt.ascii "()")

@[expose, rust_fun "core::result::{core::result::Result<@T, @E>}::expect"]
def core.result.Result.expect {T : Type _} {E : Type _} (_DebugInst : core.fmt.Debug E)
  (r : core.result.Result T E) (_ : Str) : Std.Result T :=
  match r with
  | .Ok x => .ok x
  | .Err _ =>
    /- TODO: this is a simplistic model -/
    .fail .panic

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field1_finish", simp]
def core.fmt.Formatter.debug_struct_field1_finish
  (fmt : core.fmt.Formatter) (name : Str)
  (name1 : Str) (value1 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.debugStruct fmt name.val [(name1.val, value1.inst.fmt value1.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish", simp]
def core.fmt.Formatter.debug_struct_field2_finish
  (fmt : core.fmt.Formatter) (name : Str)
  (name1 : Str) (value1 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name2 : Str) (value2 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.debugStruct fmt name.val [(name1.val, value1.inst.fmt value1.value), (name2.val, value2.inst.fmt value2.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field3_finish", simp]
def core.fmt.Formatter.debug_struct_field3_finish
  (fmt : core.fmt.Formatter) (name : Str)
  (name1 : Str) (value1 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name2 : Str) (value2 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name3 : Str) (value3 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.debugStruct fmt name.val [(name1.val, value1.inst.fmt value1.value), (name2.val, value2.inst.fmt value2.value), (name3.val, value3.inst.fmt value3.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field4_finish", simp]
def core.fmt.Formatter.debug_struct_field4_finish
  (fmt : core.fmt.Formatter) (name : Str)
  (name1 : Str) (value1 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name2 : Str) (value2 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name3 : Str) (value3 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name4 : Str) (value4 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.debugStruct fmt name.val [(name1.val, value1.inst.fmt value1.value), (name2.val, value2.inst.fmt value2.value), (name3.val, value3.inst.fmt value3.value), (name4.val, value4.inst.fmt value4.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field5_finish", simp]
def core.fmt.Formatter.debug_struct_field5_finish
  (fmt : core.fmt.Formatter) (name : Str)
  (name1 : Str) (value1 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name2 : Str) (value2 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name3 : Str) (value3 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name4 : Str) (value4 : Dyn (fun dyn => core.fmt.Debug dyn))
  (name5 : Str) (value5 : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.debugStruct fmt name.val [(name1.val, value1.inst.fmt value1.value), (name2.val, value2.inst.fmt value2.value), (name3.val, value3.inst.fmt value3.value), (name4.val, value4.inst.fmt value4.value), (name5.val, value5.inst.fmt value5.value)]

@[expose, rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_tuple_field1_finish", simp]
def core.fmt.Formatter.debug_tuple_field1_finish
  (fmt : core.fmt.Formatter) (name : Str) (value : Dyn (fun dyn => core.fmt.Debug dyn)) :
  Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  RustFmt.debugTuple1 fmt name.val (value.inst.fmt value.value)

@[expose, reducible, rust_trait_impl "core::fmt::Debug<&'0 @T>"]
def core.fmt.DebugShared {T : Type _} (DebugInst : core.fmt.Debug T) :
  core.fmt.Debug T := {
  fmt := core.fmt.DebugShared.fmt DebugInst
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<()>"]
def core.fmt.DebugUnit : core.fmt.Debug Unit := {
  fmt := core.fmt.DebugUnit.fmt
}

@[expose, reducible, rust_trait_impl "core::fmt::Debug<bool>"]
def core.fmt.DebugBool : core.fmt.Debug Bool := {
  fmt := core.fmt.DebugBool.fmt
}

@[expose, rust_fun "core::fmt::rt::{core::fmt::rt::Argument<'0>}::new_display"]
def core.fmt.rt.Argument.new_display
  {T : Type _} (DisplayInst : core.fmt.Display T) :
  T → Result core.fmt.rt.Argument :=
  fun value => .ok { format := DisplayInst.fmt value }

end Aeneas.Std
