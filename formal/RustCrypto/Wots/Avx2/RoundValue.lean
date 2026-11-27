module
public import RustCrypto.Wots.Avx2.ScanInvariant
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000

theorem scan_tail_values (original scanned finalNodes : Aeneas.Std.Array Node 16#usize)
    (digits : WotsRecover.Digits) (offset : Usize) (step : U8) (chains : Aeneas.Std.Array Usize 4#usize)
    (count : Usize) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hinv : scanInvariant original scanned digits offset step chains count 16#usize seed key)
    (htail : ∀ j < 16, nativeNode (finalNodes[j]!) =
      if queued chains count.val j then chainHash seed key (offset.val+j) step.val (nativeNode (scanned[j]!))
      else nativeNode (scanned[j]!)) :
    ∀ j < 16, nativeNode (finalNodes[j]!) =
      if eligible digits offset step j then chainHash seed key (offset.val+j) step.val (nativeNode (original[j]!))
      else nativeNode (original[j]!) := by
  classical
  rcases hinv with ⟨_,_,_,hqueued,_,hvalues⟩
  intro j hj
  rw [htail j hj]
  by_cases hq : queued chains count.val j
  · have ha := (hqueued j hq).2
    have hw : nativeNode (scanned[j]!) = nativeNode (original[j]!) := by
      rw [hvalues j hj]
      exact scan_value_waiting _ _ _ chains count.val (16#usize).val j (Or.inl hq)
    simp only [ite_eq_left hq,hw,ite_eq_left ha]
  · simp only [ite_eq_right hq]
    rw [hvalues j hj]
    unfold scanValue
    simp only [show (16#usize).val = 16 from rfl,hj,true_and,hq,not_false_eq_true,and_true]

end RustCrypto.WotsAvx2
