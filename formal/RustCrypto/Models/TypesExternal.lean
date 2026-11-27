module
public import Aeneas
public import RustCrypto.Models.Simd
@[expose] public section
open Aeneas.Std

/-! Alloy incremental hashing retains the complete byte stream. The external
library boundary is specified by EthLib Keccak, rather than an unconstrained
function. This model does not verify Alloy or its machine implementation. -/
abbrev alloy_primitives.utils.Keccak256 := List U8
