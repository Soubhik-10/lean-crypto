module
public import RustCrypto.HashPrimitives
public import RustCrypto.Codeword
public import EthLib.Cryptography.Wots
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.CounterSearch
set_option maxHeartbeats 2000000
abbrev Node := Aeneas.Std.Array U8 16#usize
abbrev Digits := Aeneas.Std.Array U8 64#usize
abbrev Address := lean_sphincs.hash.HashContext

@[irreducible] def encoded (headBytes : List U8) (message : Node) (counter : Aeneas.Std.Array U8 4#usize) : Node :=
  Aeneas.Std.Array.from ((digest (headBytes ++ message.val ++ counter.val)).val.take 16) (by simp)

def counterWord (counter : Nat) : U32 := ⟨BitVec.ofNat 32 counter⟩

@[irreducible] def accept (headBytes : List U8) (message : Node) (counter : U32) : Option Digits :=
  let code := encoded headBytes message (core.num.U32.to_be_bytes counter)
  if Codeword.sumPrefix (Codeword.expectedDigits code) 64 = 128
  then some (Codeword.expectedDigits code) else none

@[step] theorem counter_cast_spec (counter : U64) :
    lift (UScalar.cast .U32 counter) ⦃ out => out = counterWord counter.val ⦄ := by
  simp only [lift, WP.spec_ok]
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, UScalar.cast_bv_eq, BitVec.toNat_setWidth,
    counterWord]
  rfl

theorem encode_input_eq (address : Address) (message : Node) (counter : Aeneas.Std.Array U8 4#usize) :
    ((address.val.setSlice! 48 message.val).setSlice! 64 counter.val).take 68 =
      address.val.take 48 ++ message.val ++ counter.val := by
  simp [List.setSlice!, List.take_append, List.drop_append, List.append_assoc,
    List.take_of_length_le]

@[step] theorem encode_node_spec (address : Address) (message : Node)
    (counter : Aeneas.Std.Array U8 4#usize) :
    lean_sphincs.hash.HashContext.encode address message counter ⦃ out =>
      out.1 = encoded (address.val.take 48) message counter ∧
      out.2.val.take 48 = address.val.take 48 ⦄ := by
  apply WP.spec_mono (RustCrypto.encode_spec address message counter)
  rintro ⟨code, next⟩ ⟨hcode, hnext⟩
  constructor
  · apply Aeneas.Std.Array.ext
    rw [hcode, encode_input_eq]
    unfold encoded
    rfl
  · simp only [hnext]
    simp [List.setSlice!, List.take_append, List.drop_append,
      List.append_assoc, List.take_of_length_le]

/-- One source counter iteration either advances once or returns precisely its accepted word. -/
@[step] theorem body_spec (address : Address) (message : Node) (limit counter : U64)
    (hrun : counter.val < limit.val) :
    lean_sphincs.wots.find_encoding_loop.body message limit address counter ⦃ result =>
      match result with
      | .cont (nextAddress, nextCounter) =>
          accept (address.val.take 48) message (counterWord counter.val) = none ∧
          nextAddress.val.take 48 = address.val.take 48 ∧ nextCounter.val = counter.val + 1
      | .done (out, nextAddress) =>
          ∃ digits, accept (address.val.take 48) message (counterWord counter.val) = some digits ∧
            out = some (counterWord counter.val, digits) ∧
            nextAddress.val.take 48 = address.val.take 48 ⦄ := by
  unfold lean_sphincs.wots.find_encoding_loop.body
  have hbranch : counter < limit := by scalar_tac
  simp only [ite_eq_left hbranch]
  step with counter_cast_spec
  step
  have ha : a = core.num.U32.to_be_bytes i := by
    apply Aeneas.Std.Array.ext
    simpa [core.num.U32.to_be_bytes] using a_post
  subst a
  step with encode_node_spec
  step with Codeword.codeword_spec
  have hopt : o = accept (address.val.take 48) message (counterWord counter.val) := by
    simpa only [accept, fb_post, i_post] using o_post
  rw [hopt]
  cases htrial : accept (address.val.take 48) message (counterWord counter.val) with
  | none =>
    step
    exact ⟨fb_post1, by assumption⟩
  | some digits =>
    step with counter_cast_spec
    refine ⟨digits, rfl, ?_, fb_post1⟩
    simp_all only


def search (headBytes : List U8) (message : Node) (start fuel : Nat) : Option (U32 × Digits) :=
  EthLib.Cryptography.Wots.findFirst (m := Id) counterWord
    (fun counter => accept headBytes message counter) start fuel

theorem search_zero (headBytes : List U8) (message : Node) (start : Nat) :
    search headBytes message start 0 = none := by rfl

theorem search_succ (headBytes : List U8) (message : Node) (start fuel : Nat) :
    search headBytes message start (fuel+1) =
      match accept headBytes message (counterWord start) with
      | some digits => some (counterWord start, digits)
      | none => search headBytes message (start+1) fuel := by
  unfold search
  rw [EthLib.Cryptography.Wots.findFirst]
  cases accept headBytes message (counterWord start) <;> rfl

/-- The actual bounded search is total, including exhaustion and narrowing-cast wraparound. -/
@[step] theorem loop_spec (address : Address) (message : Node) (limit counter : U64) :
    lean_sphincs.wots.find_encoding_loop address message limit counter ⦃ out =>
      out.1 = search (address.val.take 48) message counter.val (limit.val-counter.val) ∧
      out.2.val.take 48 = address.val.take 48 ⦄ := by
  let headBytes := address.val.take 48
  let expected := search headBytes message counter.val (limit.val-counter.val)
  unfold lean_sphincs.wots.find_encoding_loop
  apply loop.spec_decr_nat
    (fun state : Address × U64 => limit.val-state.2.val)
    (fun state : Address × U64 => state.1.val.take 48 = headBytes ∧
      expected = search headBytes message state.2.val (limit.val-state.2.val))
  · rintro ⟨currentAddress, currentCounter⟩ ⟨hprefix, hmodel⟩
    dsimp only at hprefix hmodel
    dsimp only
    by_cases hrun : currentCounter.val < limit.val
    · apply WP.spec_mono (body_spec currentAddress message limit currentCounter hrun)
      intro result hresult
      have hf : limit.val-currentCounter.val =
          (limit.val-(currentCounter.val+1))+1 := by omega
      cases result with
      | cont state =>
        rcases state with ⟨nextAddress, nextCounter⟩
        rcases hresult with ⟨hnone, hhead, hnext⟩
        have hn : accept headBytes message (counterWord currentCounter.val) = none := by
          simpa only [hprefix] using hnone
        refine ⟨⟨hhead.trans hprefix, ?_⟩, by scalar_tac⟩
        rw [hmodel, hf, search_succ, hn, hnext]
      | done value =>
        rcases value with ⟨out, nextAddress⟩
        rcases hresult with ⟨digits, haccepted, hout, hhead⟩
        have ha : accept headBytes message (counterWord currentCounter.val) = some digits := by
          simpa only [hprefix] using haccepted
        refine ⟨?_, hhead.trans hprefix⟩
        change out = expected
        rw [hout, hmodel, hf, search_succ, ha]
    · have hstop : ¬ currentCounter < limit := by scalar_tac
      have hz : limit.val-currentCounter.val = 0 := by omega
      simp only [lean_sphincs.wots.find_encoding_loop.body, ite_eq_right hstop, WP.spec_ok]
      refine ⟨?_, hprefix⟩
      change none = expected
      simpa only [hz, search_zero] using hmodel.symm
  · exact ⟨rfl, rfl⟩

/-- Source counter search refines EthLib's first-success search with the exact source encoding. -/
@[step] theorem find_encoding_spec (address : Address) (message : Node) (limit : U64) :
    lean_sphincs.wots.find_encoding address message limit ⦃ out =>
      out.1 = search (address.val.take 48) message 0 limit.val ∧
      out.2.val.take 48 = address.val.take 48 ⦄ := by
  unfold lean_sphincs.wots.find_encoding
  apply WP.spec_mono (loop_spec address message limit 0#u64)
  intro out hout
  simpa using hout

end RustCrypto.CounterSearch
