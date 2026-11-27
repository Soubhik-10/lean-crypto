module
public import RustCrypto.Wots.Recovery.Model
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[irreducible] def chainHash (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (chain step : Nat)
    (value : EthLib.Cryptography.Sphincs.Digest) : EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
    (EthLib.Cryptography.Sphincs.keyAdrs .wotsHash key chain step) (EthLib.Base.packBytes value)

def progress (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (word : EthLib.Cryptography.Sphincs.Codeword)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) (value : EthLib.Cryptography.Sphincs.Digest) : Nat → EthLib.Cryptography.Sphincs.Digest
  | 0 => value
  | step+1 => if (word[chain]).val ≤ step then chainHash seed key chain.val step (progress seed key word chain value step)
      else progress seed key word chain value step

/-- Three masked rounds are exactly the canonical recovery interval for each of the four possible digits. -/
theorem progress_end (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (word : EthLib.Cryptography.Sphincs.Codeword)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) (value : EthLib.Cryptography.Sphincs.Digest) :
    progress seed key word chain value 3 = WotsRecover.endValue seed key word chain value := by
  have hd : (word[chain]).val < 4 := (word[chain]).isLt
  have hc : (word[chain]).val = 0 ∨ (word[chain]).val = 1 ∨ (word[chain]).val = 2 ∨ (word[chain]).val = 3 := by omega
  rcases hc with h|h|h|h
  all_goals simp only [progress,h]
  all_goals unfold WotsRecover.endValue
  all_goals simp only [h]
  all_goals solve
    | rfl
    | (simp [EthLib.Cryptography.Sphincs.chain,EthLib.Cryptography.Wots.chain,chainHash,
        EthLib.Cryptography.Sphincs.chainStep,EthLib.Cryptography.Sphincs.adrsChain]; rfl)
    | simp [EthLib.Cryptography.Sphincs.chain,EthLib.Cryptography.Wots.chain,chainHash,
        EthLib.Cryptography.Sphincs.chainStep,EthLib.Cryptography.Sphincs.adrsChain]

end RustCrypto.WotsAvx2
