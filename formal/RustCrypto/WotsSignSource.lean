module
public import RustCrypto.PublicLeafBridge
public import RustCrypto.CounterSearch
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsSignSource
open RustCrypto.WotsChain
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
abbrev Digits := Aeneas.Std.Array U8 64#usize

@[irreducible] def signStep (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (digits : Digits) (chain : Nat) : Node × Address :=
  let first := WotsSource.chainStart address seed pair (stepWord chain)
  walk (digits[chain]!).val 0 (stepWord chain) first.2 first.1

@[step] theorem body_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (digits : Digits) (output : Slice U8) (chain : Usize)
    (hrun : chain.val < 64) (hout : 1028 ≤ output.val.length) :
    lean_sphincs.wots.sign_loop.body seed pair digits address output chain ⦃ out =>
      match out with
      | .cont (nextAddress,nextOutput,nextChain) =>
          nextChain.val = chain.val+1 ∧
          nextAddress = (signStep address seed pair digits chain.val).2 ∧
          nextOutput.val = output.val.setSlice! (4+chain.val*16)
            (signStep address seed pair digits chain.val).1.val
      | .done _ => False ⦄ := by
  unfold lean_sphincs.wots.sign_loop.body
  simp only [lean_sphincs.params.WOTS_CHAINS, lean_sphincs.params.NODE_BYTES,
    alloy_primitives.bits.fixed.FixedBytes.as_slice]
  have hbranch : chain < 64#usize := by scalar_tac
  simp only [ite_eq_left hbranch]
  step
  step with WotsSource.chain_start_spec
  step
  step
  step with RustCrypto.WotsChain.walk_chain_spec
  step*
  · scalar_tac
  · have hi : i = stepWord chain.val := by
      apply UScalar.eq_of_val_eq
      simp only [i_post, UScalar.cast_val_eq, stepWord]
      rfl
    have hi1 : i1 = stepWord chain.val := by
      simpa only [i1_post, i_post] using hi
    have hdigit : i2 = digits[chain.val]! := by
      rw [Aeneas.Std.Array.getElem!_Nat_eq,
        getElem!_pos digits.val chain.val (by scalar_tac)]
      exact i2_post
    have hn := congrArg Prod.fst node_post
    have ha := congrArg Prod.snd node_post
    dsimp only at hn ha
    have hnext : (node1,address2) = signStep address seed pair digits chain.val := by
      simpa only [signStep, hi, hi1, hdigit, hn, ha, Nat.sub_zero] using node1_post
    refine ⟨i5_post, congrArg Prod.snd hnext, ?_⟩
    rw [s_post2, s2_post]
    have hv := congrArg (fun next : Node × Address => next.1.val) hnext
    simpa [i4_post,i3_post] using
      congrArg (fun bytes => output.val.setSlice! (4+chain.val*16) bytes) hv

@[irreducible] def signCollect (seed : Aeneas.Std.Array U8 32#usize) (pair : U32) (digits : Digits) :
    Nat → Nat → Address → List U8 → Address × List U8
  | 0, _, address, output => (address,output)
  | fuel+1, chain, address, output =>
      let next := signStep address seed pair digits chain
      signCollect seed pair digits fuel (chain+1) next.2
        (output.setSlice! (4+chain*16) next.1.val)

/-- All 64 source signing iterations terminate and write exactly their specified chain bytes. -/
@[step] theorem loop_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (digits : Digits) (output : Slice U8) (chain : Usize)
    (hout : 1028 ≤ output.val.length) :
    lean_sphincs.wots.sign_loop address seed pair output digits chain ⦃ out =>
      (out.1,out.2.val) = signCollect seed pair digits (64-chain.val) chain.val address output.val ⦄ := by
  let expected := signCollect seed pair digits (64-chain.val) chain.val address output.val
  unfold lean_sphincs.wots.sign_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × Usize => 64-state.2.2.val)
    (fun state : Address × Slice U8 × Usize => 1028 ≤ state.2.1.val.length ∧
      expected = signCollect seed pair digits (64-state.2.2.val) state.2.2.val state.1 state.2.1.val)
  · rintro ⟨currentAddress,currentOutput,currentChain⟩ ⟨hlen,hmodel⟩
    dsimp only at hlen hmodel
    dsimp only
    by_cases hrun : currentChain.val < 64
    · apply WP.spec_mono (body_spec currentAddress seed pair digits currentOutput currentChain hrun hlen)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextOutput,nextChain⟩
        rcases hresult with ⟨hc,ha,ho⟩
        dsimp only
        refine ⟨⟨?_,?_⟩,by scalar_tac⟩
        · simpa only [ho, List.length_setSlice!] using hlen
        · rw [hmodel]
          have hf : 64-currentChain.val = (64-(currentChain.val+1))+1 := by omega
          rw [hf, signCollect]
          simp only [hc,ha,ho]
    · have hstop : ¬ currentChain < lean_sphincs.params.WOTS_CHAINS := by
        simp only [lean_sphincs.params.WOTS_CHAINS]
        scalar_tac
      have hz : 64-currentChain.val = 0 := by omega
      simp only [lean_sphincs.wots.sign_loop.body, ite_eq_right hstop, WP.spec_ok]
      simpa only [hz, signCollect] using hmodel.symm
  · exact ⟨hout,rfl⟩

/-- Complete source WOTS signing: earliest counter, exhaustion, and exact chain-byte writes. -/
@[step] theorem sign_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (message : Node) (output : Slice U8) (limit : U64)
    (hout : 1028 ≤ output.val.length) :
    lean_sphincs.wots.sign address seed pair message output limit ⦃ out =>
      let initial := WotsSource.domain address 7#u32 pair
      match CounterSearch.search (initial.val.take 48) message 0 limit.val with
      | none => out.1 = none ∧ out.2.2 = output ∧ out.2.1.val.take 48 = initial.val.take 48
      | some (counter,digits) => out.1 = some () ∧ ∃ searched : Address,
          searched.val.take 48 = initial.val.take 48 ∧
          (out.2.1,out.2.2.val) = signCollect seed pair digits 64 0 searched
            (output.val.setSlice! 0 (core.num.U32.to_be_bytes counter).val) ⦄ := by
  unfold lean_sphincs.wots.sign
  simp only [lean_sphincs.wots.WOTS_ENCODING]
  step with WotsSource.domain_spec
  step with CounterSearch.find_encoding_spec
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  cases ho : o with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    step*
  | some value =>
    rcases value with ⟨counter,digits⟩
    step*
    have hs := o_post.symm.trans ho
    rw [address1_post] at hs
    rw [hs]
    refine ⟨address2, ?_, ?_⟩
    · simpa only [address1_post] using o_post1
    · have ha : a = core.num.U32.to_be_bytes counter := by
        apply Aeneas.Std.Array.ext
        simpa only [core.num.U32.to_be_bytes, Aeneas.Std.Array.from_val] using a_post
      simpa [s_post2,s2_post,s1_post,ha] using address3_post

end RustCrypto.WotsSignSource
