module
public import RustCrypto.WotsAvx2ScanLoop
public import RustCrypto.WotsAvx2TailLoop
public import RustCrypto.WotsAvx2RoundValue
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem round_body_spec (address : Address) (addresses : Aeneas.Std.Array Address 4#usize)
    (nodes : Aeneas.Std.Array Node 16#usize) (digits : WotsRecover.Digits) (offset : Usize) (step : U8)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hstep : step.val < 3) (hoffset : offset.val+16 ≤ 64)
    (hframe : keyFrame address seed key .wotsHash)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_window_loop0.body digits offset address addresses nodes step ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextAddresses,nextNodes,nextStep) =>
          nextStep.val = step.val+1 ∧ keyFrame nextAddress seed key .wotsHash ∧
          (∀ j < 4, keyFrame (nextAddresses[j]!) seed key .wotsHash) ∧
          ∀ j < 16, nativeNode (nextNodes[j]!) =
            if eligible digits offset step j then chainHash seed key (offset.val+j) step.val (nativeNode (nodes[j]!))
            else nativeNode (nodes[j]!) ⦄ := by
  classical
  unfold lean_sphincs.wots.recover_window_loop0.body
  have hrun : step < lean_sphincs.params.CHAIN_END := by
    simp only [lean_sphincs.params.CHAIN_END]
    scalar_tac
  simp only [ite_eq_left hrun]
  let chains : Aeneas.Std.Array Usize 4#usize := Aeneas.Std.Array.repeat 4#usize 0#usize
  have hchains : ∀ j < 4, (chains[j]!).val < 16 := by
    intro j hj
    have hz : chains[j]! = 0#usize := by
      simp only [chains,Aeneas.Std.Array.getElem!_Nat_eq,Aeneas.Std.Array.repeat_val]
      change (List.replicate 4 (0#usize))[j]! = 0#usize
      rw [getElem!_pos _ j (by simpa only [List.length_replicate] using hj)]
      exact List.getElem_replicate (by simpa only [List.length_replicate] using hj)
    rw [hz]
    decide
  have hinitial := initial_scan_invariant nodes digits offset step chains seed key hchains
  step with scan_loop_spec nodes nodes addresses digits offset step chains 0#usize 0#usize seed key hoffset hinitial hframes
    as ⟨nextAddresses,scannedNodes,nextChains,count,hscanned,hscanFrames⟩
  step with tail_zero_spec scannedNodes address offset step nextChains count seed key
    (by have hb := hscanned.2.1; omega) hoffset hscanned.2.2.1 hscanned.2.2.2.2.1 hframe
    as ⟨nextAddress,nextNodes,hnextFrame,hnextValues⟩
  step as ⟨nextStep,hnextStep⟩
  refine ⟨hnextStep,hnextFrame,hscanFrames,?_⟩
  exact scan_tail_values nodes scannedNodes nextNodes digits offset step nextChains count seed key hscanned hnextValues

end RustCrypto.WotsAvx2
