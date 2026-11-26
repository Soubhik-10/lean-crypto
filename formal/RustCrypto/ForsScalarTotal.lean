module
public import RustCrypto.ForsScalarShortLoop
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsScalar
open RustCrypto.ForsRead RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem recover_trees_short_spec (address : Address) (reader : Slice U8) (roots : List U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hreader : reader.val.length < 4224)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees address reader digest roots ⦃ out =>
      out.1 = none ∧ keyFrame out.2.1 seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ∧
      out.2.2.1.val = reader.val.drop (16*(reader.val.length/16)) ⦄ := by
  unfold lean_sphincs.fors.recover_trees
  step with short_loop_spec address reader roots digest seed idx hreader hframe
    as ⟨status,nextAddress,remaining,nextRoots,hstatus,hnextFrame,hremaining⟩
  exact ⟨hstatus,hnextFrame,hremaining⟩

/-- The actual FORS entry point returns `None` on every truncated input. -/
@[step] theorem recover_fors_short_spec (address : Address) (reader : Slice U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hreader : reader.val.length < 4224)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.fors.recover_fors address reader digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) ⦃ out =>
      out.1 = none ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
      out.2.2.val = reader.val.drop (16*(reader.val.length/16)) ⦄ := by
  let key := EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx
  unfold lean_sphincs.fors.recover_fors
  simp only [lean_sphincs.fors.FORS_PUBLIC_KEY,lean_sphincs.fors.FORS_TREE]
  step with ForsPrimitives.domain_frame_spec address seed .bottom key.tree 4#u32 (stepWord key.leaf) hframe
    as ⟨publicAddress,hpublic⟩
  step with accumulator_spec publicAddress as ⟨roots,hroots⟩
  have hpublicFrame : TreePrimitives.frame publicAddress seed .bottom key.tree := ⟨4#u32,stepWord key.leaf,0#u32,0#u32,hpublic⟩
  step with ForsPrimitives.domain_frame_spec publicAddress seed .bottom key.tree 3#u32 (stepWord key.leaf) hpublicFrame
    as ⟨treeAddress,htree⟩
  have hl : key.layer = .bottom := rfl
  have htag : addressTag .forsTree = 3#u32 := rfl
  have htreeFrame : keyFrame treeAddress seed key .forsTree := by
    refine ⟨0#u32,0#u32,?_⟩
    simpa only [hl,htag] using htree
  step with recover_trees_short_spec treeAddress reader roots digest seed idx hreader htreeFrame
    as ⟨status,nextAddress,remaining,nextRoots,hstatus,hnextFrame,hremaining⟩
  rw [hstatus]
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
  refine ⟨True.intro,?_,hremaining⟩
  rcases hnextFrame with ⟨word2,word3,hnextHeader⟩
  have hl2 : (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).layer = .bottom := rfl
  exact ⟨addressTag .forsTree,stepWord key.leaf,word2,word3,by simpa only [hl2] using hnextHeader⟩

/-- Total functional specification of source scalar FORS recovery for every input byte length. -/
@[step] theorem recover_fors_total_spec (address : Address) (reader : Slice U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.fors.recover_fors address reader digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) ⦃ out =>
      out.1.map nativeNode = (if 4224 ≤ reader.val.length then some (canonicalRecover reader.val digest seed idx) else none) ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
      out.2.2.val = reader.val.drop (if 4224 ≤ reader.val.length then 4224 else 16*(reader.val.length/16)) ⦄ := by
  by_cases hroom : 4224 ≤ reader.val.length
  · apply WP.spec_mono (recover_fors_ethlib_spec address reader digest seed idx hroom hframe)
    intro out hout
    simpa only [ite_eq_left hroom] using hout
  · apply WP.spec_mono (recover_fors_short_spec address reader digest seed idx (by omega) hframe)
    rintro out ⟨hresult,hnext,hremaining⟩
    refine ⟨?_,hnext,?_⟩
    · simp only [ite_eq_right hroom,hresult,Option.map_none]
    · simpa only [ite_eq_right hroom] using hremaining

end RustCrypto.ForsScalar
