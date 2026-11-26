module
public import RustCrypto.FmtLaws
public import Aeneas.Std.Scalar.Notations
@[expose] public section
open Aeneas Aeneas.Std Aeneas.Std.RustFmt
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace RustCrypto.ErrorFormatting

def errorPrefix : Bytes := ascii "no admissible WOTS+C counter for layer "

def signTemplate : Bytes := [39#u8,110#u8,111#u8,32#u8,97#u8,100#u8,109#u8,105#u8,115#u8,115#u8,105#u8,98#u8,108#u8,101#u8,32#u8,87#u8,79#u8,84#u8,83#u8,43#u8,67#u8,32#u8,99#u8,111#u8,117#u8,110#u8,116#u8,101#u8,114#u8,32#u8,102#u8,111#u8,114#u8,32#u8,108#u8,97#u8,121#u8,101#u8,114#u8,32#u8,192#u8,0#u8]

theorem template_program (arg : Argument) (fmt : Formatter) :
    writeArguments fmt { template := signTemplate, values := [arg] } =
      thenDo (writeBytes fmt errorPrefix) (fun afterPrefix => runArgument afterPrefix {} arg) := by
  simp [writeArguments,signTemplate,runTemplate,thenDo_done,errorPrefix,ascii]
  rfl

end RustCrypto.ErrorFormatting
