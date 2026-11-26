module
public import LeanSphincs.Funs
public import RustCrypto.FmtTemplate
import all Init.Data.ByteArray.Basic
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.RustFmt
open lean_sphincs
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace RustCrypto.ErrorFormatting

def displayProgram (layer : U8) (fmt : Formatter) : Result (FmtResult × Formatter) :=
  thenDo (writeBytes fmt errorPrefix) (fun afterPrefix => do
    let (result,next) ← writeBytes { afterPrefix with options := {} } (ascii (Nat.repr layer.val))
    .ok (result,{ next with options := afterPrefix.options }))

theorem source_display_program (layer : U8) (fmt : Formatter) :
    signing.SignError.Insts.CoreFmtDisplay.fmt (.CounterExhausted layer) fmt =
      displayProgram layer fmt := by
  simp only [signing.SignError.Insts.CoreFmtDisplay.fmt,
    core.fmt.rt.Argument.new_display,core.fmt.Arguments.new,
    core.fmt.Formatter.write_fmt,Array.make_val]
  dsimp only [core.fmt.rt.Argument,core.fmt.Arguments,core.fmt.Formatter]
  simp only [bind_ok]
  change writeArguments fmt {
    template := signTemplate
    values := [{ format := displayNat layer.val }] } = displayProgram layer fmt
  rw [template_program]
  unfold displayProgram
  congr 1
  funext afterPrefix
  simp only [runArgument,default_display_nat,decimal_u8]
  congr 1


theorem error_name_bytes : (toStr "CounterExhausted").val = ascii "CounterExhausted" := by
  simp only [toStr,Slice.from_val]
  decide +kernel

theorem error_field_bytes : (toStr "layer").val = ascii "layer" := by
  simp only [toStr,Slice.from_val]
  decide +kernel


def debugProgram (layer : U8) (fmt : Formatter) : Result (FmtResult × Formatter) :=
  RustFmt.debugStruct fmt (ascii "CounterExhausted")
    [(ascii "layer",RustFmt.debugNat layer.val)]

theorem source_debug_program (layer : U8) (fmt : Formatter) :
    signing.SignError.Insts.CoreFmtDebug.fmt (.CounterExhausted layer) fmt =
      debugProgram layer fmt := by
  simp only [signing.SignError.Insts.CoreFmtDebug.fmt,
    core.fmt.Formatter.debug_struct_field1_finish,error_name_bytes,error_field_bytes]
  rfl


theorem source_clone (error : signing.SignError) :
    signing.SignError.Insts.CoreCloneClone.clone error = .ok error := by rfl

theorem source_equality (left right : U8) :
    signing.SignError.Insts.CoreCmpPartialEqSignError.eq
      (.CounterExhausted left) (.CounterExhausted right) = .ok (left == right) := by
  by_cases h : left = right <;>
    simp [signing.SignError.Insts.CoreCmpPartialEqSignError.eq, core.cmp.impls.PartialEqU8.eq,lift,h]

theorem source_equality_iff (left right : U8) :
    signing.SignError.Insts.CoreCmpPartialEqSignError.eq
      (.CounterExhausted left) (.CounterExhausted right) = .ok true ↔ left = right := by
  rw [source_equality]
  simp

theorem source_eq_assertion (error : signing.SignError) :
    signing.SignError.Insts.CoreCmpEq.assert_fields_are_eq error = .ok () := by rfl

theorem source_error_debug (error : signing.SignError) (fmt : Formatter) :
    signing.SignError.Insts.CoreErrorError.fmtDebugInst.fmt error fmt =
      signing.SignError.Insts.CoreFmtDebug.fmt error fmt := by rfl

theorem source_error_display (error : signing.SignError) (fmt : Formatter) :
    signing.SignError.Insts.CoreErrorError.fmtDisplayInst.fmt error fmt =
      signing.SignError.Insts.CoreFmtDisplay.fmt error fmt := by rfl

end RustCrypto.ErrorFormatting
