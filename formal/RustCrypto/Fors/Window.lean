module
public import Aeneas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace RustCrypto.ForsDigest
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def windowBit (a b c p : Nat) : Nat :=
  if p < 8 then (a / 2^(7-p)) % 2
  else if p < 16 then (b / 2^(15-p)) % 2
  else (c / 2^(23-p)) % 2

def windowField (a b c offset : Nat) : Nat :=
  (List.range 10).foldl (fun value j => 2*value+windowBit a b c (offset+j)) 0

theorem window_field_eq (a b c offset : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hoffset : offset < 8) :
    windowField a b c offset = ((65536*a+256*b+c) / 2^(14-offset)) % 1024 := by
  interval_cases offset <;> norm_num [windowField,windowBit,List.range_succ] <;> omega

end RustCrypto.ForsDigest
