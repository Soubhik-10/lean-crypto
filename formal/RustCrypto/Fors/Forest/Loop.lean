module
public import RustCrypto.Fors.Forest.Body
public import RustCrypto.Fors.Forest.Prefix
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def invariant (reader : Slice U8) (roots : List U8) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (state : Slice U8 × List U8 × Aeneas.Std.Array Address 2#usize × Usize) : Prop :=
  state.2.2.2.val ≤ 24 ∧ state.2.2.2.val % width = 0 ∧
  state.1.val = reader.val.drop (176*state.2.2.2.val) ∧
  (∀ j : Fin width, keyFrame (state.2.2.1[j.val]!) seed (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) ∧
  nativeBytes state.2.1 = nativeBytes roots ++ rootsBefore reader.val digest seed idx state.2.2.2.val

/-- The entire extracted SIMD forest loop recovers all 24 roots in canonical tree order. -/
@[step] theorem forest_loop_spec (reader : Slice U8) (roots : List U8)
    (addresses : Aeneas.Std.Array Address 2#usize) (digest : Aeneas.Std.Array U8 34#usize) (seed : Node) (idx : Nat)
    (hreader : 4224 ≤ reader.val.length)
    (hframes : ∀ j : Fin width, keyFrame (addresses[j.val]!) seed
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx) .forsTree) :
    lean_sphincs.fors.recover_trees_loop reader digest roots addresses 0#usize ⦃ out =>
      out.1 = some () ∧ out.2.1.val = reader.val.drop 4224 ∧
      nativeBytes out.2.2 = nativeBytes roots ++ rootsBefore reader.val digest seed idx 24 ⦄ := by
  unfold lean_sphincs.fors.recover_trees_loop
  apply loop.spec_decr_nat
    (fun state : Slice U8 × List U8 × Aeneas.Std.Array Address 2#usize × Usize => 24-state.2.2.2.val)
    (invariant reader roots digest seed idx)
  · rintro ⟨currentReader,currentRoots,currentAddresses,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hmod,hread,hcurrentFrames,hroots⟩
    dsimp only at hcount hmod hread hcurrentFrames hroots
    dsimp only
    by_cases hrun : currentIndex.val < 24
    · have hstart : currentIndex.val+width ≤ 24 := by
        simp only [width] at hmod ⊢
        omega
      have hbytes : 352 ≤ currentReader.val.length := by
        rw [hread,List.length_drop]
        have hb := hstart
        simp only [width] at hb
        omega
      apply WP.spec_mono (forest_body_spec currentReader currentRoots currentAddresses digest seed idx currentIndex hstart hbytes hcurrentFrames)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨nextReader,nextRoots,nextAddresses,nextIndex⟩
        rcases hresult with ⟨hindex,hnextReader,nodes,hnextRoots,hnodes,hnextFrames⟩
        have hgroup := native_group nodes (recoveredRoots reader.val digest seed idx) currentIndex.val
          (by exact hstart) (by
            intro j hj
            have hjwidth : j < width := hj
            have hrow := hnodes ⟨j,hjwidth⟩
            have hroom : 176*currentIndex.val+176*j+176 ≤ reader.val.length := by
              have hb := hstart
              have hjwidth : j < width := hj
              simp only [width] at hb hjwidth
              omega
            rw [hread,openingAt_drop reader.val (176*currentIndex.val) (176*j) hroom] at hrow
            have hoffset : 176*currentIndex.val+176*j = 176*(currentIndex.val+j) := by omega
            rw [hoffset] at hrow
            simpa only [recoveredRoots,Vector.getElem_ofFn,recovered,treeAt,leafAt] using hrow)
        have hw : (2#usize).val = width := rfl
        rw [hw] at hgroup
        have hnewRoots : nativeBytes nextRoots = nativeBytes roots ++ rootsBefore reader.val digest seed idx (currentIndex.val+width) := by
          rw [hnextRoots]
          rw [show nativeBytes (currentRoots ++ nodes.val.flatMap (fun node => node.val)) =
            nativeBytes currentRoots ++ nativeBytes (nodes.val.flatMap (fun node => node.val)) from List.map_append]
          rw [hroots,hgroup,List.append_assoc,← roots_before_add]
        have hnewReader : nextReader.val = reader.val.drop (176*nextIndex.val) := by
          rw [hnextReader,hread,List.drop_drop,hindex]
          congr 1
        dsimp only
        constructor
        · dsimp only [invariant]
          refine ⟨by omega,?_,hnewReader,hnextFrames,?_⟩
          · rw [hindex]
            simp only [width] at hmod ⊢
            omega
          · simpa only [hindex] using hnewRoots
        · rw [hindex]
          have hwpos : 0 < width := by decide
          omega
    · have hc : currentIndex.val = 24 := by omega
      have hstop : ¬currentIndex < lean_sphincs.params.FORS_TREES := by
        simp only [lean_sphincs.params.FORS_TREES]
        scalar_tac
      simp only [lean_sphincs.fors.recover_trees_loop.body,ite_eq_right hstop,WP.spec_ok]
      refine ⟨True.intro,?_,?_⟩
      · simpa only [hc,Nat.reduceMul] using hread
      · simpa only [hc] using hroots
  · change invariant reader roots digest seed idx (reader,roots,addresses,0#usize)
    have hz : (0#usize).val = 0 := rfl
    refine ⟨by scalar_tac,?_,?_,hframes,?_⟩
    · simp only [hz,Nat.zero_mod]
    · simp only [hz,Nat.mul_zero,List.drop_zero]
    · simp only [hz,rootsBefore,OrderedPrefix.prefix_zero,List.append_nil]

end RustCrypto.ForsForest
