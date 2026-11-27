module
public import EthLib.Cryptography.Wots
@[expose] public section
namespace RustCrypto.ChainOrder
set_option maxHeartbeats 2000000

theorem chain_cons {α : Type} {n : Nat} (step : Fin n → α → Id α)
    (start fuel : Nat) (h : start+(fuel+1) ≤ n) (value : α) :
    EthLib.Cryptography.Wots.chain step start (fuel+1) h value =
      EthLib.Cryptography.Wots.chain step (start+1) fuel (by omega)
        (step ⟨start,by omega⟩ value) := by
  induction fuel generalizing start value with
  | zero => rfl
  | succ fuel ih =>
    change step ⟨start+(fuel+1),by omega⟩
        (EthLib.Cryptography.Wots.chain step start (fuel+1) (by omega) value) =
      step ⟨start+1+fuel,by omega⟩
        (EthLib.Cryptography.Wots.chain step (start+1) fuel (by omega)
          (step ⟨start,by omega⟩ value))
    rw [ih]
    congr 1
    apply Fin.ext
    dsimp only
    omega

end RustCrypto.ChainOrder
