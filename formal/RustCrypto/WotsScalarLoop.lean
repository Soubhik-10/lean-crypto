module
public import RustCrypto.WotsScalarBody
public import RustCrypto.WotsRecoverLayout
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def scalarInvariant (reader : Slice U8) (ends : List U8) (word : EthLib.Cryptography.Sphincs.Codeword)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (state : Address × Slice U8 × List U8 × Usize) : Prop :=
  state.2.2.2.val ≤ 64 ∧ state.2.1.val = reader.val.drop (16*state.2.2.2.val) ∧
  keyFrame state.1 seed key .wotsHash ∧
  nativeBytes state.2.2.1 = nativeBytes ends ++ endsBefore reader.val word seed key state.2.2.2.val

/-- All 64 actual scalar-recovery chains are consumed and hashed in canonical chain order. -/
@[step] theorem scalar_loop_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hreader : 1024 ≤ reader.val.length) (hdigits : digitRelation digits word) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop address reader digits ends 0#usize ⦃ out =>
      out.1 = some () ∧ keyFrame out.2.1 seed key .wotsHash ∧ out.2.2.1.val = reader.val.drop 1024 ∧
      nativeBytes out.2.2.2 = nativeBytes ends ++ endsBefore reader.val word seed key 64 ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Usize => 64-state.2.2.2.val)
    (scalarInvariant reader ends word seed key)
  · rintro ⟨currentAddress,currentReader,currentEnds,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hread,hcurrentFrame,hends⟩
    dsimp only at hcount hread hcurrentFrame hends
    dsimp only
    by_cases hrun : currentIndex.val < 64
    · have hbytes : 16 ≤ currentReader.val.length := by rw [hread,List.length_drop]; omega
      apply WP.spec_mono (scalar_body_spec currentAddress currentReader currentEnds digits word seed key currentIndex hrun hbytes hdigits hcurrentFrame)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextReader,nextEnds,nextIndex⟩
        rcases hresult with ⟨hindex,hnextReader,hnextFrame,root,hroot,hnextEnds⟩
        have hrootRef : nativeNode root = endValue seed key word
            ⟨currentIndex.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.V] using hrun⟩
            (nativeNode (ForsRead.nodeAt reader.val (16*currentIndex.val))) := by
          rw [hread,ForsRead.nodeAt_drop reader.val (16*currentIndex.val) 0 (by omega),Nat.add_zero] at hroot
          exact hroot
        have hn : nativeBytes root.val = (endValue seed key word
            ⟨currentIndex.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.V] using hrun⟩
            (nativeNode (ForsRead.nodeAt reader.val (16*currentIndex.val)))).toList := by
          simpa only [nativeBytes,native_node_list] using congrArg Vector.toList hrootRef
        have hnewEnds : nativeBytes nextEnds = nativeBytes ends ++ endsBefore reader.val word seed key (currentIndex.val+1) := by
          rw [hnextEnds]
          rw [show nativeBytes (currentEnds ++ root.val) = nativeBytes currentEnds ++ nativeBytes root.val from List.map_append]
          rw [hends,hn,List.append_assoc,← ends_before_succ reader.val word seed key currentIndex.val hrun]
        have hnewReader : nextReader.val = reader.val.drop (16*nextIndex.val) := by
          rw [hnextReader,hread,List.drop_drop,hindex]
          congr 1
        dsimp only
        constructor
        · dsimp only [scalarInvariant]
          exact ⟨by omega,hnewReader,hnextFrame,by simpa only [hindex] using hnewEnds⟩
        · rw [hindex]
          omega
    · have hc : currentIndex.val = 64 := by omega
      have hstop : ¬currentIndex < lean_sphincs.params.WOTS_CHAINS := by
        simp only [lean_sphincs.params.WOTS_CHAINS]
        scalar_tac
      simp only [lean_sphincs.wots.recover_chains_loop.body,ite_eq_right hstop,WP.spec_ok]
      refine ⟨True.intro,hcurrentFrame,?_,?_⟩
      · simpa only [hc,Nat.reduceMul] using hread
      · simpa only [hc] using hends
  · change scalarInvariant reader ends word seed key (address,reader,ends,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,hframe,?_⟩
    · simp only [hz,Nat.mul_zero,List.drop_zero]
    · simp only [hz,endsBefore,OrderedPrefix.prefix_zero,List.append_nil]

end RustCrypto.WotsRecover
