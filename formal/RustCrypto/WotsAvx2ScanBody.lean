module
public import RustCrypto.WotsAvx2Group
public import RustCrypto.WotsAvx2Queue
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

abbrev eligible (digits : WotsRecover.Digits) (offset : Usize) (step : U8) (j : Nat) : Prop :=
  (digits[offset.val+j]!).val ≤ step.val

/-- One actual scan iteration either queues a chain or flushes its four-lane group. -/
@[step] theorem scan_body_spec (addresses : Aeneas.Std.Array Address 4#usize)
    (nodes : Aeneas.Std.Array Node 16#usize) (digits : WotsRecover.Digits) (offset : Usize) (step : U8)
    (chains : Aeneas.Std.Array Usize 4#usize) (count chain : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hchain : chain.val < 16) (hcount : count.val < 4) (hoffset : offset.val+16 ≤ 64)
    (hchains : ∀ j < 4, (chains[j]!).val < 16)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_window_loop0_loop0.body digits offset step addresses nodes chains count chain ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddresses,nextNodes,nextChains,nextCount,nextChain) =>
          nextChain.val = chain.val+1 ∧
          (∀ j < 4, keyFrame (nextAddresses[j]!) seed key .wotsHash) ∧
          (if eligible digits offset step chain.val then
            nextChains = chains.set count chain ∧
            (if count.val+1 = 4 then nextCount.val = 0 ∧
              ∀ j < 16, nativeNode (nextNodes[j]!) =
                if selected4 nextChains j then chainHash seed key (offset.val+j) step.val (nativeNode (nodes[j]!))
                else nativeNode (nodes[j]!)
             else nextCount.val = count.val+1 ∧ nextNodes = nodes)
           else nextChains = chains ∧ nextCount = count ∧ nextNodes = nodes) ⦄ := by
  classical
  unfold lean_sphincs.wots.recover_window_loop0_loop0.body
  have hrun : chain < lean_sphincs.wots.CHAINS_PER_WINDOW := by
    simp only [lean_sphincs.wots.CHAINS_PER_WINDOW]
    scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨index,hindex⟩
  step as ⟨digit,hdigit⟩
  have hd : digit = digits[offset.val+chain.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos digits.val (offset.val+chain.val) (by scalar_tac)]
    simpa only [hindex] using hdigit
  by_cases hactive : eligible digits offset step chain.val
  · have ht : digit <= step := by
      rw [hd]
      exact hactive
    simp only [ite_eq_left ht]
    step as ⟨borrow,hborrow,hrestore⟩
    rcases borrow with ⟨slot,restore⟩
    dsimp only at hborrow hrestore ⊢
    simp only [hrestore]
    step as ⟨nextCount,hnextCount⟩
    have hnewchains := append_bounded chains count chain hcount hchain hchains
    by_cases hflush : count.val+1 = 4
    · have heq : nextCount = lean_sphincs.hash.batch.WIDTH := by
        apply UScalar.eq_of_val_eq
        simp only [lean_sphincs.hash.batch.WIDTH]
        scalar_tac
      simp only [ite_eq_left heq,ite_eq_left hactive,ite_eq_left hflush]
      step with recover_group_spec addresses nodes (chains.set count chain) offset step seed key hnewchains hoffset hframes
        as ⟨nextState,values,hscatter,hvalues,hnextFrames⟩
      rcases nextState with ⟨nextAddresses,nextNodes⟩
      dsimp only at hscatter hvalues hnextFrames ⊢
      step as ⟨nextChain,hnextChain⟩
      refine ⟨hnextChain,hnextFrames,rfl,?_⟩
      intro j hj
      let f : Nat → EthLib.Cryptography.Sphincs.Digest :=
        fun k => chainHash seed key (offset.val+k) step.val (nativeNode (nodes[k]!))
      have hv : ∀ lane < 4, nativeNode (values[lane]!) = f ((chains.set count chain)[lane]!).val := by
        intro lane hlane
        exact hvalues lane hlane
      have hs := scatter_four_native nodes (chains.set count chain) values f hv j hj
      calc
        nativeNode (nextNodes[j]!) = nativeNode ((scatter (chains.set count chain) values 4 0 nodes)[j]!) :=
          congrArg (fun ns : Aeneas.Std.Array Node 16#usize => nativeNode (ns[j]!)) hscatter
        _ = _ := hs
    · have hne : nextCount ≠ lean_sphincs.hash.batch.WIDTH := by
        intro heq
        have he := congrArg UScalar.val heq
        simp only [lean_sphincs.hash.batch.WIDTH] at he
        scalar_tac
      simp only [ite_eq_right hne,ite_eq_left hactive,ite_eq_right hflush]
      step*
  · have ht : ¬digit <= step := by
      rw [hd]
      exact hactive
    simp only [ite_eq_right ht]
    simp only [ite_eq_right hactive]
    step*

end RustCrypto.WotsAvx2
