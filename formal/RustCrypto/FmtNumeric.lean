module
public import Aeneas.Std.Core.FmtModel
import all Init.Data.Repr
@[expose] public section
open Aeneas.Std Aeneas.Std.RustFmt
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace RustCrypto.ErrorFormatting

theorem decimal_byte_table : ∀ n : Fin 256,
    digits .decimal false n.val = ascii (Nat.repr n.val) := by
  intro n
  fin_cases n <;> rfl

theorem decimal_u8 (value : U8) : digits .decimal false value.val = ascii (Nat.repr value.val) := by
  have bound : value.val < 256 := by
    simpa only [UScalarTy.U8_numBits_eq, Nat.reducePow] using value.hBounds
  exact decimal_byte_table ⟨value.val,bound⟩

theorem decimal_line_table : ∀ n : Fin 256,
    splitLines (digits .decimal false n.val) = [digits .decimal false n.val] ∧
      endsLine (digits .decimal false n.val) = false := by
  intro n
  fin_cases n <;> constructor <;> rfl

theorem decimal_ascii_line (value : U8) :
    splitLines (ascii (Nat.repr value.val)) = [ascii (Nat.repr value.val)] ∧
      endsLine (ascii (Nat.repr value.val)) = false := by
  have bound : value.val < 256 := by
    simpa only [UScalarTy.U8_numBits_eq, Nat.reducePow] using value.hBounds
  simpa only [decimal_u8] using decimal_line_table ⟨value.val,bound⟩


theorem write_bytes_append (fmt : Formatter) (bytes : Bytes)
    (hw : fmt.writer = appendWriter) (hi : fmt.indents = []) :
    writeBytes fmt bytes = .ok (.Ok (),
      { fmt with
        state := { bytes := fmt.state.bytes ++ bytes, aux := fmt.state.aux }
        trace := fmt.trace ++ [.str bytes] }) := by
  simp [writeBytes,writeEvent,route,hw,hi,appendWriter,eventBytes]

end RustCrypto.ErrorFormatting
