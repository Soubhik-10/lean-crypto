module
public import RustCrypto.Wots.Avx2.Read
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem read_window_spec (reader : Slice U8) (hreader : 256 ≤ reader.val.length) :
    lean_sphincs.wots.read_window reader ⦃ out =>
      out.1 = some (windowNodes reader.val) ∧ out.2.val = reader.val.drop 256 ⦄ := by
  unfold lean_sphincs.wots.read_window
  rw [RustParser.take_success 256#usize reader hreader]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  step as ⟨slice,hslice⟩
  rw [hslice]
  simp only [core.slice.Slice.as_chunks]
  have hn : ¬(16#usize).val = 0 := by decide
  simp only [ite_eq_right hn]
  step with first_window_spec (RustParser.readPrefix 256#usize reader hreader) as ⟨option,values,hoption,hvalues⟩
  rw [hoption]
  step with copy_array_spec values as ⟨copied,hcopied⟩
  have harray : copied = windowNodes reader.val := by
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp only [windowNodes,Aeneas.Std.Array.from_val,nodeList_length]
      scalar_tac
    · intro j hj hother
      have hj16 : j < 16 := by scalar_tac
      have he : copied[j]! = (windowNodes reader.val)[j]! := by
        rw [hcopied j hj16]
        apply Aeneas.Std.Array.ext
        rw [hvalues j hj16,window_get reader.val j hj16,ForsRead.nodeAt_val reader.val (16*j) (by omega)]
        have h256 : (256#usize).val = 256 := rfl
        simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,h256,List.drop_take,List.take_take]
        rw [Nat.min_eq_left (by omega)]
      simpa only [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos copied.val j hj,
        getElem!_pos (windowNodes reader.val).val j hother] using he
  refine ⟨congrArg some harray,?_⟩
  have h256 : (256#usize).val = 256 := rfl
  simp only [RustParser.readSuffix,Slice.from_val,h256]

@[step] theorem read_window_short_spec (reader : Slice U8) (hreader : reader.val.length < 256) :
    lean_sphincs.wots.read_window reader ⦃ out => out = (none,reader) ⦄ := by
  unfold lean_sphincs.wots.read_window
  rw [RustParser.take_failure 256#usize reader hreader]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]

/-- The actual AVX2 parser reads exactly one complete 16-chain window, or consumes nothing. -/
@[step] theorem read_window_total_spec (reader : Slice U8) :
    lean_sphincs.wots.read_window reader ⦃ out =>
      out.1 = (if 256 ≤ reader.val.length then some (windowNodes reader.val) else none) ∧
      out.2.val = reader.val.drop (if 256 ≤ reader.val.length then 256 else 0) ⦄ := by
  by_cases hroom : 256 ≤ reader.val.length
  · apply WP.spec_mono (read_window_spec reader hroom)
    intro out hout
    simpa only [ite_eq_left hroom] using hout
  · apply WP.spec_mono (read_window_short_spec reader (by omega))
    intro out hout
    rw [hout]
    simp only [ite_eq_right hroom,List.drop_zero,true_and]

end RustCrypto.WotsAvx2
