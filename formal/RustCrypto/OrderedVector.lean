module
public import RustCrypto.WotsPrf
@[expose] public section
namespace RustCrypto.OrderedVector
set_option maxHeartbeats 2000000

theorem go_id {α : Type} (n : Nat) (f : Fin n → Id α) (fuel : Nat) :
    ∀ (acc : Array α) (h : acc.size+fuel=n),
      acc.toList = (List.ofFn f).take acc.size →
      (EthLib.Cryptography.HashSig.ofFnInOrder.go n f fuel acc h).toList = List.ofFn f := by
  induction fuel with
  | zero =>
    intro acc h hacc
    simp only [EthLib.Cryptography.HashSig.ofFnInOrder.go]
    have hs : acc.size = n := by omega
    change acc.toList = List.ofFn f
    rw [hacc, hs, List.take_of_length_le (by simp)]
  | succ fuel ih =>
    intro acc h hacc
    rw [EthLib.Cryptography.HashSig.ofFnInOrder.go]
    apply ih
    simp only [Array.toList_push, Array.size_push]
    rw [List.take_succ_eq_append_getElem (by simp; omega), hacc]
    simp only [List.getElem_ofFn]

/-- EthLib's ordered identity-monad construction returns exactly the indexed vector. -/
theorem ofFnInOrder_id {α : Type} (n : Nat) (f : Fin n → Id α) :
    EthLib.Cryptography.HashSig.ofFnInOrder n f = Vector.ofFn f := by
  apply Vector.toList_inj.1
  simpa only [EthLib.Cryptography.HashSig.ofFnInOrder, Vector.toList_ofFn] using
    go_id n f n (Array.emptyWithCapacity n) (by simp) (by simp)

end RustCrypto.OrderedVector
