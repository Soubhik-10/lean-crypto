module
public import RustCrypto.Fors.Signing.Core
public import RustCrypto.Common.OrderedPrefix
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsSigning
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.TreePrimitives RustCrypto.WotsEthlib
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def rows (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize) :
    Vector (EthLib.Cryptography.Sphincs.TreeOpening × EthLib.Cryptography.Sphincs.Digest)
      EthLib.Cryptography.Sphincs.Constants.FORS_TREES := Vector.ofFn (opening seed secret idx digest)

def encodedPrefix (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize)
    (count : Nat) : List UInt8 :=
  OrderedPrefix.collect (rows seed secret idx digest) (fun row => (EthLib.Cryptography.Sphincs.treeOpeningBytes row.1).toList) count

def rootsPrefix (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize)
    (count : Nat) : List UInt8 :=
  OrderedPrefix.collect (rows seed secret idx digest) (fun row => row.2.toList) count

theorem encoded_succ (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize)
    (count : Nat) (hcount : count < 24) :
    encodedPrefix seed secret idx digest (count+1) = encodedPrefix seed secret idx digest count ++
      (EthLib.Cryptography.Sphincs.treeOpeningBytes (opening seed secret idx digest ⟨count,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hcount⟩).1).toList := by
  unfold encodedPrefix
  rw [OrderedPrefix.prefix_succ (rows seed secret idx digest)
    (fun row => (EthLib.Cryptography.Sphincs.treeOpeningBytes row.1).toList) count
    (by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hcount)]
  simp only [rows,Vector.getElem_ofFn]

theorem roots_succ (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize)
    (count : Nat) (hcount : count < 24) :
    rootsPrefix seed secret idx digest (count+1) = rootsPrefix seed secret idx digest count ++
      (opening seed secret idx digest ⟨count,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hcount⟩).2.toList := by
  unfold rootsPrefix
  rw [OrderedPrefix.prefix_succ (rows seed secret idx digest) (fun row => row.2.toList) count
    (by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hcount)]
  simp only [rows,Vector.getElem_ofFn]

theorem encoded_length (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize)
    (count : Nat) (hcount : count ≤ 24) : (encodedPrefix seed secret idx digest count).length = count*176 := by
  apply OrderedPrefix.prefix_length
  · intro row
    exact Vector.length_toList
  · exact hcount

def invariant (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat) (digest : Aeneas.Std.Array U8 34#usize)
    (output : Slice U8) (roots : List U8) (state : Address × Slice U8 × List U8 × Usize) : Prop :=
  state.2.2.2.val ≤ 24 ∧ state.2.1.val.length = output.val.length ∧
  TreePrimitives.frame state.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
  asBytes state.2.1.val = encodedPrefix seed secret idx digest state.2.2.2.val ++ (asBytes output.val).drop (176*state.2.2.2.val) ∧
  asBytes state.2.2.1 = asBytes roots ++ rootsPrefix seed secret idx digest state.2.2.2.val

/-- All 24 actual FORS signing iterations terminate with exact opening bytes and ordered root inputs. -/
@[step] theorem loop_spec (address : Address) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (digest : Aeneas.Std.Array U8 34#usize) (idx : Nat) (output : Slice U8) (roots : List U8)
    (hsize : 4224 ≤ output.val.length)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.fors.sign_loop address secret digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) output roots 0#usize ⦃ out =>
      TreePrimitives.frame out.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
      asBytes out.2.1.val = encodedPrefix seed secret idx digest 24 ++ (asBytes output.val).drop 4224 ∧
      asBytes out.2.2 = asBytes roots ++ rootsPrefix seed secret idx digest 24 ⦄ := by
  unfold lean_sphincs.fors.sign_loop
  apply loop.spec_decr_nat
    (fun state : Address × Slice U8 × List U8 × Usize => 24-state.2.2.2.val)
    (invariant seed secret idx digest output roots)
  · rintro ⟨current,currentOutput,currentRoots,currentIndex⟩ hinv
    rcases hinv with ⟨hcount,hlen,hcurrent,hbytes,hroots⟩
    dsimp only at hcount hlen hcurrent hbytes hroots
    dsimp only
    by_cases hrun : currentIndex.val < 24
    · apply WP.spec_mono (body_spec current seed secret digest idx currentOutput currentRoots currentIndex hrun (by omega) hcurrent)
      intro result hresult
      cases result with
      | done value => exact False.elim hresult
      | cont state =>
        rcases state with ⟨next,nextOutput,nextRoots,nextIndex⟩
        rcases hresult with ⟨hindex,hnext,hnextBytes,hnextRoots⟩
        have hencodedLen : (EthLib.Cryptography.Sphincs.treeOpeningBytes
            (opening seed secret idx digest ⟨currentIndex.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hrun⟩).1).toList.length = 176 := Vector.length_toList
        have hlength := congrArg List.length hnextBytes
        simp only [asBytes,List.length_map,List.length_append,List.length_take,List.length_drop,hencodedLen] at hlength
        have hstart : 176*currentIndex.val ≤ currentOutput.val.length := by omega
        rw [Nat.min_eq_left hstart] at hlength
        have hnextLength : nextOutput.val.length = output.val.length := by omega
        have hpLen : (encodedPrefix seed secret idx digest currentIndex.val).length = 176*currentIndex.val := by
          simpa only [Nat.mul_comm] using encoded_length seed secret idx digest currentIndex.val hcount
        have hend : 176*(currentIndex.val+1) = 176*currentIndex.val+
            (EthLib.Cryptography.Sphincs.treeOpeningBytes (opening seed secret idx digest ⟨currentIndex.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.FORS_TREES] using hrun⟩).1).toList.length := by
          rw [hencodedLen]
          omega
        have hfinalBytes : asBytes nextOutput.val = encodedPrefix seed secret idx digest (currentIndex.val+1) ++
            (asBytes output.val).drop (176*(currentIndex.val+1)) := by
          rw [hnextBytes,hend,hbytes,OrderedPrefix.replace_next _ _ _ _ hpLen]
          rw [← encoded_succ seed secret idx digest currentIndex.val hrun,← hend]
        have hfinalRoots : asBytes nextRoots = asBytes roots ++ rootsPrefix seed secret idx digest (currentIndex.val+1) := by
          rw [hnextRoots,hroots,List.append_assoc,← roots_succ seed secret idx digest currentIndex.val hrun]
        constructor
        · dsimp only [invariant]
          rw [hindex]
          exact ⟨by omega,hnextLength,hnext,hfinalBytes,hfinalRoots⟩
        · dsimp only
          rw [hindex]
          omega
    · have hstop : ¬currentIndex < lean_sphincs.params.FORS_TREES := by
        simp only [lean_sphincs.params.FORS_TREES]
        scalar_tac
      have hc : currentIndex.val = 24 := by omega
      simp only [lean_sphincs.fors.sign_loop.body,ite_eq_right hstop,WP.spec_ok]
      exact ⟨hcurrent,by simpa only [hc,Nat.reduceMul] using hbytes,by simpa only [hc] using hroots⟩
  · change invariant seed secret idx digest output roots (address,output,roots,0#usize)
    refine ⟨by scalar_tac,rfl,hframe,?_,?_⟩
    · change asBytes output.val = encodedPrefix seed secret idx digest 0 ++ (asBytes output.val).drop 0
      simp only [encodedPrefix,OrderedPrefix.prefix_zero,List.nil_append,List.drop_zero]
    · change asBytes roots = asBytes roots ++ rootsPrefix seed secret idx digest 0
      simp only [rootsPrefix,OrderedPrefix.prefix_zero,List.append_nil]

end RustCrypto.ForsSigning
