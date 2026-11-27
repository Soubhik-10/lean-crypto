module
public import RustCrypto.Fors.Scalar.Body
public import RustCrypto.Fors.Scalar.Layout
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsScalar
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def invariant (reader : Slice U8) (roots : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (state : Address × Slice U8 × List U8 × Usize) : Prop :=
  state.2.2.2.val ≤ 24 ∧ state.2.1.val = reader.val.drop (176*state.2.2.2.val) ∧
  keyFrame state.1 seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ∧
  nativeBytes state.2.2.1 = nativeBytes roots ++ rootsBefore reader.val digest seed idx state.2.2.2.val

@[step] theorem loop_spec (address : Address) (reader : Slice U8) (roots : List U8)
    (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat) (hreader : 4224 ≤ reader.val.length)
    (hframe : keyFrame address seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop address reader digest roots 0#usize ⦃ out =>
      out.1 = some () ∧ keyFrame out.2.1 seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree ∧
      out.2.2.1.val = reader.val.drop 4224 ∧
      nativeBytes out.2.2.2 = nativeBytes roots ++ rootsBefore reader.val digest seed idx 24 ⦄ := by
  unfold lean_sphincs.fors.recover_trees_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Usize => 24-state.2.2.2.val)
    (invariant reader roots digest seed idx)
  · rintro ⟨currentAddress,currentReader,currentRoots,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hread,hcurrentFrame,hroots⟩
    dsimp only at hcount hread hcurrentFrame hroots
    dsimp only
    by_cases hrun : currentIndex.val < 24
    · have hbytes : 176 ≤ currentReader.val.length := by rw [hread,List.length_drop]; omega
      apply WP.spec_mono (body_spec currentAddress currentReader currentRoots digest seed idx currentIndex hrun hbytes hcurrentFrame)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextAddress,nextReader,nextRoots,nextIndex⟩
        rcases hresult with ⟨hindex,hnextReader,hnextFrame,root,hroot,hnextRoots⟩
        have hrootRef : nativeNode root = recovered reader.val digest seed idx
            ⟨currentIndex.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hrun⟩ := by
          rw [hread,decodedOpening_drop reader.val (176*currentIndex.val) (by omega)] at hroot
          simpa only [recovered,treeAt,leafAt] using hroot
        have hn : nativeBytes root.val = (recovered reader.val digest seed idx
            ⟨currentIndex.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hrun⟩).toList := by
          simpa only [nativeBytes,native_node_list] using congrArg Vector.toList hrootRef
        have hnewRoots : nativeBytes nextRoots = nativeBytes roots ++ rootsBefore reader.val digest seed idx (currentIndex.val+1) := by
          rw [hnextRoots]
          rw [show nativeBytes (currentRoots ++ root.val) = nativeBytes currentRoots ++ nativeBytes root.val from List.map_append]
          rw [hroots,hn,List.append_assoc,← roots_before_succ reader.val digest seed idx currentIndex.val hrun]
        have hnewReader : nextReader.val = reader.val.drop (176*nextIndex.val) := by
          rw [hnextReader,hread,List.drop_drop,hindex]
          congr 1
        dsimp only
        constructor
        · dsimp only [invariant]
          exact ⟨by omega,hnewReader,hnextFrame,by simpa only [hindex] using hnewRoots⟩
        · rw [hindex]
          omega
    · have hc : currentIndex.val = 24 := by omega
      have hstop : ¬currentIndex < lean_sphincs.params.FORS_TREES := by
        simp only [lean_sphincs.params.FORS_TREES]
        scalar_tac
      simp only [lean_sphincs.fors.recover_trees_loop.body,ite_eq_right hstop,WP.spec_ok]
      refine ⟨True.intro,hcurrentFrame,?_,?_⟩
      · simpa only [hc,Nat.reduceMul] using hread
      · simpa only [hc] using hroots
  · change invariant reader roots digest seed idx (address,reader,roots,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,hframe,?_⟩
    · simp only [hz,Nat.mul_zero,List.drop_zero]
    · simp only [hz,rootsBefore,OrderedPrefix.prefix_zero,List.append_nil]

end RustCrypto.ForsScalar
