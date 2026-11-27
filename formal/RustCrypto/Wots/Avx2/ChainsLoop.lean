module
public import RustCrypto.Wots.Avx2.ChainsBody
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

def chainsInvariant (reader : Slice U8) (ends : List U8) (word : EthLib.Cryptography.Sphincs.Codeword)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (state : Address × Slice U8 × List U8 × Aeneas.Std.Array Address 4#usize × Usize) : Prop :=
  state.2.2.2.2.val ≤ 4 ∧ state.2.1.val = reader.val.drop (256*state.2.2.2.2.val) ∧
  keyFrame state.1 seed key .wotsHash ∧
  (∀ j < 4, keyFrame (state.2.2.2.1[j]!) seed key .wotsHash) ∧
  nativeBytes state.2.2.1 = nativeBytes ends ++ WotsRecover.endsBefore reader.val word seed key (16*state.2.2.2.2.val)

@[step] theorem chains_loop_spec (address : Address) (reader : Slice U8) (ends : List U8)
    (addresses : Aeneas.Std.Array Address 4#usize) (digits : WotsRecover.Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hreader : 1024 ≤ reader.val.length) (hdigits : WotsRecover.digitRelation digits word)
    (hframe : keyFrame address seed key .wotsHash)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop address reader digits ends addresses 0#usize ⦃ out =>
      out.1 = some () ∧ keyFrame out.2.1 seed key .wotsHash ∧ out.2.2.1.val = reader.val.drop 1024 ∧
      nativeBytes out.2.2.2 = nativeBytes ends ++ WotsRecover.endsBefore reader.val word seed key 64 ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Aeneas.Std.Array Address 4#usize × Usize => 4-state.2.2.2.2.val)
    (chainsInvariant reader ends word seed key)
  · rintro ⟨currentAddress,currentReader,currentEnds,currentAddresses,currentWindow⟩ hinv
    rcases hinv with ⟨hcount,hread,hcurrentFrame,hcurrentFrames,hends⟩
    dsimp only at hcount hread hcurrentFrame hcurrentFrames hends
    dsimp only
    by_cases hrun : currentWindow.val < 4
    · have hbytes : 256 ≤ currentReader.val.length := by rw [hread,List.length_drop]; omega
      apply WP.spec_mono (chains_body_spec currentAddress currentReader currentEnds currentAddresses digits word
        currentWindow seed key hrun hbytes hdigits hcurrentFrame hcurrentFrames)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextReader,nextEnds,nextAddresses,nextWindow⟩
        rcases hresult with ⟨hwindow,hnextReader,hnextFrame,hnextFrames,roots,hnextEnds,hroots⟩
        have hrootRef : ∀ j (hj : j < (16#usize).val), nativeNode (roots[j]!) =
            (WotsRecover.endVector reader.val word seed key)[16*currentWindow.val+j]'(by
              change 16*currentWindow.val+j < 64
              have hj16 : j < 16 := hj
              omega) := by
          intro j hj
          have hj16 : j < 16 := hj
          have hr := hroots j hj
          rw [hread,ForsRead.nodeAt_drop reader.val (256*currentWindow.val) (16*j) (by omega)] at hr
          have he : 256*currentWindow.val+16*j = 16*(16*currentWindow.val+j) := by omega
          rw [he] at hr
          simpa only [WotsRecover.endVector,Vector.getElem_ofFn] using hr
        have hpacked := RustCrypto.ForsForest.native_group roots (WotsRecover.endVector reader.val word seed key)
          (16*currentWindow.val) (by change 16*currentWindow.val+16 ≤ 64; omega) hrootRef
        change nativeBytes (roots.val.flatMap (fun node => node.val)) =
          (((WotsRecover.endVector reader.val word seed key).toList.drop (16*currentWindow.val)).take 16).flatMap Vector.toList at hpacked
        have hnewEnds : nativeBytes nextEnds = nativeBytes ends ++
            WotsRecover.endsBefore reader.val word seed key (16*currentWindow.val+16) := by
          rw [hnextEnds]
          rw [show nativeBytes (currentEnds ++ roots.val.flatMap (fun root => root.val)) =
            nativeBytes currentEnds ++ nativeBytes (roots.val.flatMap (fun root => root.val)) from List.map_append]
          rw [hends,hpacked,List.append_assoc,←ends_before_add]
        have hnewReader : nextReader.val = reader.val.drop (256*nextWindow.val) := by
          rw [hnextReader,hread,List.drop_drop,hwindow]
          congr 1
        dsimp only [chainsInvariant]
        refine ⟨⟨by omega,hnewReader,hnextFrame,hnextFrames,?_⟩,by omega⟩
        have he : 16*nextWindow.val = 16*currentWindow.val+16 := by omega
        simpa only [he] using hnewEnds
    · have hc : currentWindow.val = 4 := by omega
      unfold lean_sphincs.wots.recover_chains_loop.body
      simp only [lean_sphincs.params.WOTS_CHAINS,lean_sphincs.wots.CHAINS_PER_WINDOW]
      step as ⟨bound,hbound⟩
      have hb : bound.val = 4 := by scalar_tac
      have hstop : ¬currentWindow < bound := by scalar_tac
      simp only [ite_eq_right hstop,WP.spec_ok]
      refine ⟨True.intro,hcurrentFrame,?_,?_⟩
      · simpa only [hc,Nat.reduceMul] using hread
      · simpa only [hc,Nat.reduceMul] using hends
  · change chainsInvariant reader ends word seed key (address,reader,ends,addresses,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,hframe,hframes,?_⟩
    · simp only [hz,Nat.mul_zero,List.drop_zero]
    · simp only [hz,Nat.mul_zero,WotsRecover.endsBefore,OrderedPrefix.prefix_zero,List.append_nil]

end RustCrypto.WotsAvx2
