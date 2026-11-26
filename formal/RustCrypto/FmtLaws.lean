module
public import RustCrypto.FmtNumeric
@[expose] public section
open Aeneas.Std Aeneas.Std.RustFmt
namespace RustCrypto.ErrorFormatting

theorem thenDo_done (first : Result (FmtResult × Formatter)) :
    thenDo first (fun fmt => .ok (.Ok (),fmt)) = first := by
  unfold thenDo
  have step : (fun (p : FmtResult × Formatter) =>
      match p.1 with
      | .Ok _ => Result.ok (.Ok (),p.2)
      | .Err e => Result.ok (.Err e,p.2)) = Result.ok := by
    funext ⟨result,fmt⟩
    cases result <;> rfl
  change Aeneas.Std.bind first (fun p => match p.1 with
    | .Ok _ => Result.ok (.Ok (),p.2)
    | .Err e => Result.ok (.Err e,p.2)) = first
  rw [step]
  simp

theorem thenDo_error (fmt : Formatter) (next : FormatM) :
    thenDo (.ok (.Err (),fmt)) next = .ok (.Err (),fmt) := by
  simp [thenDo]

theorem thenDo_failure (error : Error) (next : FormatM) :
    thenDo (.fail error) next = .fail error := by simp [thenDo]

theorem default_display_nat (fmt : Formatter) (n : Nat) :
    displayNat n { fmt with options := {} } =
      writeBytes { fmt with options := {} } (digits .decimal false n) := by
  simp [displayNat,padIntegral,writePrefix,thenDo]

end RustCrypto.ErrorFormatting
