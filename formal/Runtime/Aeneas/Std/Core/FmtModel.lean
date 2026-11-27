module
public import Aeneas.Std.Core.Core
public import Aeneas.Std.Core.Result
public import Aeneas.Std.Array.Array
public import Aeneas.Std.StringDef
@[expose] public section

namespace Aeneas.Std.RustFmt

abbrev Bytes := List U8
abbrev FmtResult := core.result.Result Unit Unit

inductive WriteEvent where
  | str : Bytes → WriteEvent
  | char : Char → WriteEvent

structure SinkState where
  bytes : Bytes := []
  aux : Nat := 0

abbrev Writer := SinkState → WriteEvent → Result (FmtResult × SinkState)

def ascii (s : String) : Bytes := s.toUTF8.data.toList.map (fun byte =>
  UScalar.ofNatCore byte.toNat (by simpa only [UScalarTy.U8_numBits_eq, Nat.reducePow] using byte.toNat_lt))

def charBytes (c : Char) : Bytes := ascii (String.singleton c)

def eventBytes : WriteEvent → Bytes
  | .str bytes => bytes
  | .char c => charBytes c

def appendWriter : Writer := fun state event => .ok (.Ok (), { state with bytes := state.bytes ++ eventBytes event })

inductive Alignment where | left | right | center
  deriving DecidableEq

structure Options where
  fill : Char := ' '
  align : Option Alignment := none
  plus : Bool := false
  minus : Bool := false
  alternate : Bool := false
  zeroPad : Bool := false
  debugLowerHex : Bool := false
  debugUpperHex : Bool := false
  width : Nat := 0
  precision : Option Nat := none

structure Formatter where
  writer : Writer := appendWriter
  state : SinkState := {}
  options : Options := {}
  indents : List Bool := []
  trace : List WriteEvent := []

structure Routed where
  result : FmtResult
  state : SinkState
  indents : List Bool
  trace : List WriteEvent

def splitLines : Bytes → List Bytes
  | [] => []
  | b::rest => if b.val == 10 then [b]::splitLines rest
    else match splitLines rest with
      | [] => [[b]]
      | part::parts => (b::part)::parts

def endsLine (bytes : Bytes) : Bool := match bytes.getLast? with
  | none => false
  | some b => b.val == 10

/-- One PadAdapter layer, using the already-modelled underlying writer. -/
def routePieces (lower : List Bool → SinkState → WriteEvent → Result Routed) :
    List Bytes → Bool → List Bool → SinkState → Result Routed
  | [], onLine, rest, state => .ok ⟨.Ok (), state, onLine::rest, []⟩
  | part::parts, onLine, rest, state => do
      let pre ← if onLine then lower rest state (.str (ascii "    ")) else .ok ⟨.Ok (),state,rest,[]⟩
      match pre.result with
      | .Err error => .ok ⟨.Err error,pre.state,onLine::pre.indents,pre.trace⟩
      | .Ok _ =>
        let line := endsLine part
        let written ← lower pre.indents pre.state (.str part)
        match written.result with
        | .Err error => .ok ⟨.Err error,written.state,line::written.indents,pre.trace ++ written.trace⟩
        | .Ok _ =>
          let after ← routePieces lower parts line written.indents written.state
          .ok { after with trace := pre.trace ++ written.trace ++ after.trace }

/-- Write through exactly the nested pretty-print adapters present in a formatter. -/
def route (writer : Writer) : Nat → List Bool → SinkState → WriteEvent → Result Routed
  | 0, adapters, state, event => do
      let (result,next) ← writer state event
      .ok ⟨result,next,adapters,[event]⟩
  | _fuel+1, [], state, event => do
      let (result,next) ← writer state event
      .ok ⟨result,next,[],[event]⟩
  | fuel+1, onLine::rest, state, .str bytes =>
      routePieces (route writer fuel) (splitLines bytes) onLine rest state
  | fuel+1, onLine::rest, state, .char c => do
      let pre ← if onLine then route writer fuel rest state (.str (ascii "    ")) else .ok ⟨.Ok (),state,rest,[]⟩
      match pre.result with
      | .Err error => .ok ⟨.Err error,pre.state,onLine::pre.indents,pre.trace⟩
      | .Ok _ =>
        let written ← route writer fuel pre.indents pre.state (.char c)
        .ok { written with indents := (c == '\n')::written.indents, trace := pre.trace ++ written.trace }

abbrev FormatM := Formatter → Result (FmtResult × Formatter)

def writeEvent (fmt : Formatter) (event : WriteEvent) : Result (FmtResult × Formatter) := do
  let next ← route fmt.writer fmt.indents.length fmt.indents fmt.state event
  .ok (next.result, { fmt with state := next.state, indents := next.indents, trace := fmt.trace ++ next.trace })

def writeBytes (fmt : Formatter) (bytes : Bytes) : Result (FmtResult × Formatter) := writeEvent fmt (.str bytes)

def writeChar (fmt : Formatter) (c : Char) : Result (FmtResult × Formatter) := writeEvent fmt (.char c)

def thenDo (first : Result (FmtResult × Formatter)) (next : FormatM) : Result (FmtResult × Formatter) := do
  let (result,fmt) ← first
  match result with
  | .Ok _ => next fmt
  | .Err error => .ok (.Err error,fmt)

def repeatChar : Nat → Char → FormatM
  | 0, _, fmt => .ok (.Ok (),fmt)
  | count+1, c, fmt => thenDo (writeChar fmt c) (repeatChar count c)

inductive Radix where | decimal | hex

def Radix.base : Radix → Nat | .decimal => 10 | .hex => 16

/-- Numeric digits, with structural fuel that exceeds the number of base divisions. -/
def digitsAux (radix : Radix) (upper : Bool) : Nat → Nat → Bytes
  | 0, _ => []
  | fuel+1, n =>
    let base := radix.base
    let d := n%base
    have hd : d < 16 := by cases radix <;> simp_all [Radix.base, base, d] <;> omega
    let byte : U8 := UScalar.ofNatCore (if d < 10 then 48+d else (if upper then 65 else 97)+(d-10))
      (by simp only [UScalarTy.U8_numBits_eq, Nat.reducePow]; split <;> (try split) <;> omega)
    if n < base then [byte] else digitsAux radix upper fuel (n/base) ++ [byte]

def digits (radix : Radix) (upper : Bool) (n : Nat) : Bytes := digitsAux radix upper (n+1) n


def padding (fmt : Formatter) (count : Nat) (defaultAlign : Alignment) : Result (FmtResult × Formatter × Nat) := do
  let align := fmt.options.align.getD defaultAlign
  let before := match align with | .left => 0 | .right => count | .center => count/2
  let (result,next) ← repeatChar before fmt.options.fill fmt
  .ok (result,next,count-before)

def writePrefix (fmt : Formatter) (sign : Option Char) (numberPrefix : Option Bytes) : Result (FmtResult × Formatter) :=
  let first := match sign with | none => .ok (.Ok (),fmt) | some c => writeChar fmt c
  thenDo first (fun next => match numberPrefix with | none => .ok (.Ok (),next) | some bytes => writeBytes next bytes)

/-- Rust integer padding, including option restoration only on success in the zero-pad branch. -/
def padIntegral (fmt : Formatter) (nonnegative : Bool) (numberPrefix bytes : Bytes) : Result (FmtResult × Formatter) := do
  let sign := if !nonnegative then some '-' else if fmt.options.plus then some '+' else none
  let actualPrefix := if fmt.options.alternate then some numberPrefix else none
  let used := bytes.length + (if sign.isSome then 1 else 0) + (if fmt.options.alternate then numberPrefix.length else 0)
  if used ≥ fmt.options.width then
    thenDo (writePrefix fmt sign actualPrefix) (fun next => writeBytes next bytes)
  else if fmt.options.zeroPad then
    let oldOptions := fmt.options
    let zeroFmt := { fmt with options := { fmt.options with fill := '0', align := some .right } }
    thenDo (writePrefix zeroFmt sign actualPrefix) (fun afterPrefix => do
      let (result,afterPad,post) ← padding afterPrefix (fmt.options.width-used) .right
      match result with
      | .Err error => .ok (.Err error,afterPad)
      | .Ok _ =>
        thenDo (writeBytes afterPad bytes) (fun afterBytes => do
          let (result,afterPost) ← repeatChar post afterPad.options.fill afterBytes
          match result with
          | .Err error => .ok (.Err error,afterPost)
          | .Ok _ => .ok (.Ok (),{ afterPost with options := oldOptions })))
  else
    let (result,afterPad,post) ← padding fmt (fmt.options.width-used) .right
    match result with
    | .Err error => .ok (.Err error,afterPad)
    | .Ok _ => thenDo (writePrefix afterPad sign actualPrefix) (fun afterPrefix =>
        thenDo (writeBytes afterPrefix bytes) (repeatChar post fmt.options.fill))

def displayNat (n : Nat) : FormatM := fun fmt => padIntegral fmt true [] (digits .decimal false n)

def displayInt (n : Int) : FormatM := fun fmt => padIntegral fmt (n ≥ 0) [] (digits .decimal false n.natAbs)

def hexNat (upper : Bool) (n : Nat) : FormatM := fun fmt =>
  padIntegral fmt true (ascii (if upper then "0x" else "0x")) (digits .hex upper n)

def debugNat (n : Nat) : FormatM := fun fmt =>
  if fmt.options.debugLowerHex then hexNat false n fmt
  else if fmt.options.debugUpperHex then hexNat true n fmt
  else displayNat n fmt

def debugInt (bits : Nat) (n : Int) : FormatM := fun fmt =>
  if fmt.options.debugLowerHex then hexNat false (n%Int.ofNat (2^bits)).toNat fmt
  else if fmt.options.debugUpperHex then hexNat true (n%Int.ofNat (2^bits)).toNat fmt
  else displayInt n fmt

structure Argument where
  format : FormatM
  count : Option Nat := none

structure Arguments where
  template : Bytes := []
  values : List Argument := []
  static : Option Bytes := none

def runArgument (fmt : Formatter) (options : Options) (arg : Argument) : Result (FmtResult × Formatter) := do
  let (result,next) ← arg.format { fmt with options := options }
  .ok (result,{ next with options := fmt.options })

def readLE (bytes : Bytes) (count : Nat) : Option (Nat × Bytes) :=
  if count ≤ bytes.length then
    some (((bytes.take count).map UScalar.val).foldr (fun byte acc => byte+256*acc) 0,bytes.drop count)
  else none

def optionsFromFlags (flags width precision : Nat) : Options :=
  { fill := Char.ofNat (flags%2^21),
    align := match flags/2^29%4 with | 0 => some .left | 1 => some .right | 2 => some .center | _ => none,
    plus := flags.testBit 21, minus := flags.testBit 22, alternate := flags.testBit 23,
    zeroPad := flags.testBit 24, debugLowerHex := flags.testBit 25, debugUpperHex := flags.testBit 26,
    width := if flags.testBit 27 then width else 0, precision := if flags.testBit 28 then some precision else none }

def parseOptions (op : Nat) (current : Nat) (bytes : Bytes) (values : List Argument) : Option (Options × Nat × Bytes) := do
  let (flags,bytes) ← if op.testBit 0 then readLE bytes 4 else some (0x60000020,bytes)
  let (width,bytes) ← if op.testBit 1 then readLE bytes 2 else some (0,bytes)
  let (precision,bytes) ← if op.testBit 2 then readLE bytes 2 else some (0,bytes)
  let (argIndex,bytes) ← if op.testBit 3 then readLE bytes 2 else some (current,bytes)
  let width ← if op.testBit 4 then (values[width]?).bind Argument.count else some width
  let precision ← if op.testBit 5 then (values[precision]?).bind Argument.count else some precision
  some (optionsFromFlags flags width precision,argIndex,bytes)

/-- Rust 1.97's format-argument template interpreter; malformed unsafe inputs panic. -/
def runTemplate (values : List Argument) : Nat → Bytes → Nat → FormatM
  | 0, _, _, _ => .fail .panic
  | _fuel+1, [], _, _ => .fail .panic
  | fuel+1, op::rest, argIndex, fmt =>
    if op.val = 0 then .ok (.Ok (),fmt)
    else if op.val < 128 then
      if op.val ≤ rest.length then thenDo (writeBytes fmt (rest.take op.val))
        (runTemplate values fuel (rest.drop op.val) argIndex)
      else .fail .panic
    else if op.val = 128 then
      match readLE rest 2 with
      | none => .fail .panic
      | some (count,rest) => if count ≤ rest.length then thenDo (writeBytes fmt (rest.take count))
          (runTemplate values fuel (rest.drop count) argIndex)
        else .fail .panic
    else if op.val = 192 then
      match values[argIndex]? with
      | none => .fail .panic
      | some arg => thenDo (runArgument fmt {} arg) (runTemplate values fuel rest (argIndex+1))
    else if 192 < op.val then
      match parseOptions op.val argIndex rest values with
      | none => .fail .panic
      | some (options,index,rest) => match values[index]? with
        | none => .fail .panic
        | some arg => thenDo (runArgument fmt options arg) (runTemplate values fuel rest (index+1))
    else .fail .panic

def writeArguments (fmt : Formatter) (args : Arguments) : Result (FmtResult × Formatter) :=
  match args.static with
  | some bytes => writeBytes fmt bytes
  | none => runTemplate args.values (args.template.length+1) args.template 0 fmt

/-- Format one pretty field with a temporary PadAdapter, restoring the outer options on every return. -/
def prettyField (fmt : Formatter) (name : Bytes) (format : FormatM) : Result (FmtResult × Formatter) := do
  let wrapped := { fmt with indents := true::fmt.indents }
  let (result,next) ← thenDo (writeBytes wrapped name) (fun afterName =>
    thenDo (writeBytes afterName (ascii ": ")) (fun afterColon =>
      thenDo (format afterColon) (fun afterValue => writeBytes afterValue (ascii ",\n"))))
  .ok (result,{ next with options := fmt.options, indents := next.indents.drop 1 })

def debugFields : List (Bytes × FormatM) → Bool → FormatM
  | [], _, fmt => .ok (.Ok (),fmt)
  | (name,format)::rest, first, fmt =>
    if fmt.options.alternate then
      thenDo (if first then writeBytes fmt (ascii " {\n") else .ok (.Ok (),fmt))
        (fun afterOpen => thenDo (prettyField afterOpen name format) (debugFields rest false))
    else
      thenDo (writeBytes fmt (ascii (if first then " { " else ", "))) (fun afterOpen =>
        thenDo (writeBytes afterOpen name) (fun afterName =>
          thenDo (writeBytes afterName (ascii ": ")) (fun afterColon =>
            thenDo (format afterColon) (debugFields rest false))))

def debugStruct (fmt : Formatter) (name : Bytes) (fields : List (Bytes × FormatM)) : Result (FmtResult × Formatter) :=
  thenDo (writeBytes fmt name) (fun afterName =>
    thenDo (debugFields fields true afterName) (fun afterFields =>
      if fields.isEmpty then .ok (.Ok (),afterFields)
      else writeBytes afterFields (ascii (if afterFields.options.alternate then "}" else " }"))))


/-- String padding for the ASCII bool/unit spellings. -/
def padAscii (fmt : Formatter) (bytes : Bytes) : Result (FmtResult × Formatter) := do
  let bytes := match fmt.options.precision with | none => bytes | some n => bytes.take n
  if fmt.options.width ≤ bytes.length then writeBytes fmt bytes
  else
    let (result,afterPad,post) ← padding fmt (fmt.options.width-bytes.length) .left
    match result with
    | .Err error => .ok (.Err error,afterPad)
    | .Ok _ => thenDo (writeBytes afterPad bytes) (repeatChar post fmt.options.fill)

def debugTuple1 (fmt : Formatter) (name : Bytes) (format : FormatM) : Result (FmtResult × Formatter) :=
  thenDo (writeBytes fmt name) (fun afterName =>
    if afterName.options.alternate then
      thenDo (writeBytes afterName (ascii "(\n")) (fun afterOpen => do
        let wrapped := { afterOpen with indents := true::afterOpen.indents }
        let (result,next) ← thenDo (format wrapped) (fun afterValue => writeBytes afterValue (ascii ",\n"))
        let outer := { next with options := afterOpen.options, indents := next.indents.drop 1 }
        thenDo (.ok (result,outer)) (fun afterField => writeBytes afterField (ascii ")")))
    else
      thenDo (writeBytes afterName (ascii "(")) (fun afterOpen =>
        thenDo (format afterOpen) (fun afterValue =>
          thenDo (if name.isEmpty then writeBytes afterValue (ascii ",") else .ok (.Ok (),afterValue))
            (fun afterComma => writeBytes afterComma (ascii ")")))))

end Aeneas.Std.RustFmt
