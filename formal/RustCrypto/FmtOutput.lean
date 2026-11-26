module
public import RustCrypto.FmtSource
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.RustFmt lean_sphincs
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace RustCrypto.ErrorFormatting

def observe (computation : Result (FmtResult × Formatter)) : Result (FmtResult × Bytes) := do
  let (result,next) ← computation
  .ok (result,next.state.bytes)

theorem display_output (layer : U8) :
    observe (signing.SignError.Insts.CoreFmtDisplay.fmt (.CounterExhausted layer) {}) =
      .ok (.Ok (),errorPrefix ++ ascii (Nat.repr layer.val)) := by
  rw [source_display_program]
  simp [observe,displayProgram,writeBytes,writeEvent,route,appendWriter,eventBytes,thenDo]

theorem debug_output (layer : U8) :
    observe (signing.SignError.Insts.CoreFmtDebug.fmt (.CounterExhausted layer) {}) =
      .ok (.Ok (),ascii "CounterExhausted" ++ ascii " { " ++ ascii "layer" ++
        ascii ": " ++ ascii (Nat.repr layer.val) ++ ascii " }") := by
  rw [source_debug_program]
  simp [observe,debugProgram,debugStruct,debugFields,debugNat,displayNat,padIntegral,
    writePrefix,thenDo,writeBytes,writeEvent,route,appendWriter,eventBytes,
    decimal_u8,List.append_assoc]

theorem empty_lines : splitLines [] = [] := rfl

theorem field_line : splitLines (ascii "layer") = [ascii "layer"] ∧
    endsLine (ascii "layer") = false := by decide +kernel

theorem colon_line : splitLines (ascii ": ") = [ascii ": "] ∧
    endsLine (ascii ": ") = false := by decide +kernel

theorem comma_line : splitLines (ascii ",\n") = [ascii ",\n"] ∧
    endsLine (ascii ",\n") = true := by decide +kernel


theorem debug_pretty_output (layer : U8) :
    observe (signing.SignError.Insts.CoreFmtDebug.fmt (.CounterExhausted layer)
      { options := { alternate := true } }) =
      .ok (.Ok (),ascii "CounterExhausted" ++ ascii " {\n" ++ ascii "    " ++ ascii "layer" ++
        ascii ": " ++ ascii (Nat.repr layer.val) ++ ascii ",\n" ++ ascii "}") := by
  rw [source_debug_program]
  simp [observe,debugProgram,debugStruct,debugFields,prettyField,debugNat,displayNat,padIntegral,
    writePrefix,thenDo,writeBytes,writeEvent,route,routePieces,appendWriter,eventBytes,
    decimal_u8,(decimal_ascii_line layer).1,(decimal_ascii_line layer).2,
    field_line.1,field_line.2,colon_line.1,colon_line.2,comma_line.1,comma_line.2,
    empty_lines,List.append_assoc]


def partialFailureWriter : Writer := fun state event =>
  .ok (.Err (),{ bytes := state.bytes ++ (eventBytes event).take 1, aux := state.aux+1 })

theorem display_partial_writer_failure (layer : U8) :
    observe (signing.SignError.Insts.CoreFmtDisplay.fmt (.CounterExhausted layer)
      { writer := partialFailureWriter }) =
      .ok (.Err (),ascii "n") := by
  rw [source_display_program]
  simp [observe,displayProgram,errorPrefix,thenDo,writeBytes,writeEvent,route,
    partialFailureWriter,eventBytes,ascii]
  rfl

theorem debug_partial_writer_failure (layer : U8) :
    observe (signing.SignError.Insts.CoreFmtDebug.fmt (.CounterExhausted layer)
      { writer := partialFailureWriter }) =
      .ok (.Err (),ascii "C") := by
  rw [source_debug_program]
  simp [observe,debugProgram,debugStruct,thenDo,writeBytes,writeEvent,route,
    partialFailureWriter,eventBytes,ascii]
  rfl

theorem source_display_prefix_error (layer : U8) (fmt next : Formatter)
    (failed : writeBytes fmt errorPrefix = .ok (.Err (),next)) :
    signing.SignError.Insts.CoreFmtDisplay.fmt (.CounterExhausted layer) fmt =
      .ok (.Err (),next) := by
  rw [source_display_program]
  simp [displayProgram,failed,thenDo]
  rfl

end RustCrypto.ErrorFormatting
