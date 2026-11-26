module
public import RustCrypto.WotsChain
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsSource
open RustCrypto.WotsChain
set_option maxHeartbeats 2000000

def domain (address : Address) (tag pair : U32) : Address :=
  Aeneas.Std.Array.from (((address.val.setSlice! 32 (core.num.U32.to_be_bytes tag).val).setSlice!
    36 (core.num.U32.to_be_bytes pair).val).setSlice! 40 (List.replicate 8 0#u8)) (by simp)

@[step] theorem domain_spec (address : Address) (tag pair : U32) :
    lean_sphincs.hash.HashContext.set_domain address tag pair ⦃ out =>
      out = domain address tag pair ⦄ := by
  apply WP.spec_mono (RustCrypto.set_domain_spec address tag pair)
  intro out hout
  apply Aeneas.Std.Array.ext
  simpa only [domain, Aeneas.Std.Array.from_val] using hout

def chainStart (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair chain : U32) : Node × Address :=
  let prfAddress := positioned (domain address 5#u32 pair) chain 0#u32
  let preimage := prfAddress.val.setSlice! 48 seed.val
  let secret : Node := Aeneas.Std.Array.from ((digest preimage).val.take 16) (by simp)
  let next : Address := Aeneas.Std.Array.from preimage (by simp [preimage])
  (secret, domain next 0#u32 pair)

@[step] theorem chain_start_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair chain : U32) :
    lean_sphincs.wots.chain_start address seed pair chain ⦃ out =>
      out = chainStart address seed pair chain ⦄ := by
  unfold lean_sphincs.wots.chain_start
  simp only [lean_sphincs.wots.WOTS_PRF, lean_sphincs.wots.WOTS_CHAIN]
  step with domain_spec
  step
  step
  step with domain_spec
  have ha : address2 = positioned (domain address 5#u32 pair) chain 0#u32 := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned, Aeneas.Std.Array.from_val, address1_post] using address2_post
  apply Prod.ext
  · apply Aeneas.Std.Array.ext
    simpa only [chainStart, Aeneas.Std.Array.from_val, ha] using secret_post
  · rw [address4_post]
    apply congrArg (fun current => domain current 0#u32 pair)
    apply Aeneas.Std.Array.ext
    simpa only [chainStart, Aeneas.Std.Array.from_val, ha] using secret_post1

def publicStep (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (chain : Nat) : Node × Address :=
  let first := chainStart address seed pair (stepWord chain)
  walk 3 0 (stepWord chain) first.2 first.1

@[step] theorem public_body_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (ends : List U8) (chain : Usize) (hrun : chain.val < 64) :
    lean_sphincs.wots.public_leaf_loop.body seed pair address ends chain ⦃ out =>
      match out with
      | .cont (nextAddress,nextEnds,nextChain) =>
          nextChain.val = chain.val+1 ∧
          nextAddress = (publicStep address seed pair chain.val).2 ∧
          nextEnds = ends ++ (publicStep address seed pair chain.val).1.val
      | .done _ => False ⦄ := by
  unfold lean_sphincs.wots.public_leaf_loop.body
  simp only [lean_sphincs.params.WOTS_CHAINS, lean_sphincs.params.CHAIN_END]
  have hbranch : chain < 64#usize := by scalar_tac
  simp only [ite_eq_left hbranch]
  step
  step with chain_start_spec
  step
  step with walk_chain_spec
  simp only [alloy_primitives.utils.Keccak256.update,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreConvertAsRefSliceU8.as_ref]
  step*
  have hi : i = stepWord chain.val := by
    apply UScalar.eq_of_val_eq
    simp only [i_post, UScalar.cast_val_eq, stepWord]
    rfl
  have hi1 : i1 = stepWord chain.val := by
    simpa only [i1_post, i_post] using hi
  have hn := congrArg Prod.fst node_post
  have ha := congrArg Prod.snd node_post
  dsimp only at hn ha
  have hnext : (node1,address2) = publicStep address seed pair chain.val := by
    simpa only [publicStep, hi, hi1, hn, ha, Nat.sub_zero] using node1_post
  refine ⟨chain1_post, ?_, ?_⟩
  · exact congrArg Prod.snd hnext
  · simpa using congrArg (fun next : Node × Address => ends ++ next.1.val) hnext

@[irreducible] def publicCollect (seed : Aeneas.Std.Array U8 32#usize) (pair : U32) :
    Nat → Nat → Address → List U8 → Address × List U8
  | 0, _, address, ends => (address,ends)
  | fuel+1, chain, address, ends =>
      let next := publicStep address seed pair chain
      publicCollect seed pair fuel (chain+1) next.2 (ends ++ next.1.val)

@[step] theorem public_loop_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) (ends : List U8) (chain : Usize) :
    lean_sphincs.wots.public_leaf_loop address seed pair ends chain ⦃ out =>
      out = publicCollect seed pair (64-chain.val) chain.val address ends ⦄ := by
  let expected := publicCollect seed pair (64-chain.val) chain.val address ends
  unfold lean_sphincs.wots.public_leaf_loop
  apply loop.spec_decr_nat
    (fun state : Address × List U8 × Usize => 64-state.2.2.val)
    (fun state : Address × List U8 × Usize =>
      expected = publicCollect seed pair (64-state.2.2.val) state.2.2.val state.1 state.2.1)
  · rintro ⟨currentAddress,currentEnds,currentChain⟩ hmodel
    dsimp only at hmodel
    dsimp only
    by_cases hrun : currentChain.val < 64
    · apply WP.spec_mono (public_body_spec currentAddress seed pair currentEnds currentChain hrun)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextEnds,nextChain⟩
        rcases hresult with ⟨hc,ha,he⟩
        refine ⟨?_, by scalar_tac⟩
        rw [hmodel]
        have hf : 64-currentChain.val = (64-(currentChain.val+1))+1 := by omega
        rw [hf, publicCollect]
        simp only [hc,ha,he]
    · have hstop : ¬ currentChain < lean_sphincs.params.WOTS_CHAINS := by
        simp only [lean_sphincs.params.WOTS_CHAINS]
        scalar_tac
      have hz : 64-currentChain.val = 0 := by omega
      simp only [lean_sphincs.wots.public_leaf_loop.body, ite_eq_right hstop, WP.spec_ok]
      simpa only [hz, publicCollect] using hmodel.symm
  · rfl

@[irreducible] def publicLeaf (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) : Node × Address :=
  let initialAddress := domain address 1#u32 pair
  let ends := publicCollect seed pair 64 0 initialAddress (initialAddress.val.take 48)
  (Aeneas.Std.Array.from ((digest ends.2).val.take 16) (by simp),ends.1)

/-- Source public-key leaf generation terminates and hashes all 64 chain ends in order. -/
@[step] theorem public_leaf_spec (address : Address) (seed : Aeneas.Std.Array U8 32#usize)
    (pair : U32) : lean_sphincs.wots.public_leaf address seed pair ⦃ out =>
      out = publicLeaf address seed pair ⦄ := by
  unfold lean_sphincs.wots.public_leaf
  simp only [lean_sphincs.wots.WOTS_PUBLIC_KEY]
  step with domain_spec
  step
  step with public_loop_spec
  simp only [alloy_primitives.utils.Keccak256.finalize]
  step*
  have hc : (address2,ends1) = publicCollect seed pair 64 0
      (domain address 1#u32 pair) ((domain address 1#u32 pair).val.take 48) := by
    simpa only [address1_post, ends_post, Nat.sub_zero] using address2_post
  have ha := congrArg Prod.fst hc
  have he := congrArg Prod.snd hc
  dsimp only at ha he
  unfold publicLeaf
  apply Prod.ext
  · apply Aeneas.Std.Array.ext
    simpa only [Aeneas.Std.Array.from_val, he] using fb1_post
  · exact ha

end RustCrypto.WotsSource
