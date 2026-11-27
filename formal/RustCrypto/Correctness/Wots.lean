module
public import RustCrypto.Common.OrderedVector
public import RustCrypto.Wots.Signing.Bridge
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
open EthLib.Cryptography
open EthLib.Cryptography.Sphincs

/-- A successful bounded first-success search returned a value actually accepted by its test. -/
theorem findFirst_sound {κ β : Type} (trial : Nat → κ) (test : κ → Id (Option β))
    (fuel : Nat) : ∀ (start : Nat) (chosen : κ) (value : β),
    Wots.findFirst trial test start fuel = some (chosen,value) → test chosen = some value := by
  induction fuel with
  | zero =>
    intro start chosen value found
    simp [Wots.findFirst] at found
  | succ fuel ih =>
    intro start chosen value found
    cases tested : test (trial start) with
    | none =>
      apply ih (start+1) chosen value
      simpa [Wots.findFirst,tested,Bind.bind,Pure.pure] using found
    | some actual =>
      have pair : (trial start,actual) = (chosen,value) := by
        apply Option.some.inj
        simpa only [Wots.findFirst,tested,Bind.bind,Pure.pure] using found
      have sameTrial : trial start = chosen := congrArg Prod.fst pair
      have sameValue : actual = value := congrArg Prod.snd pair
      simpa only [sameTrial,sameValue] using tested

/-- Splitting a deterministic chain at any intermediate position preserves its final value. -/
theorem chain_append {α : Type} {n : Nat} (step : Fin n → α → Id α)
    (start first : Nat) : ∀ (last : Nat) (bound : start+first+last ≤ n) (value : α),
    Wots.chain step (start+first) last (by omega)
      (Wots.chain step start first (by omega) value) =
        Wots.chain step start (first+last) (by omega) value := by
  intro last
  induction last with
  | zero => intro bound value; rfl
  | succ last ih =>
    intro bound value
    change step ⟨start+first+last,by omega⟩
        (Wots.chain step (start+first) last (by omega)
          (Wots.chain step start first (by omega) value)) =
      step ⟨start+(first+last),by omega⟩ (Wots.chain step start (first+last) (by omega) value)
    simpa only [Nat.add_assoc] using
      congrArg (step ⟨start+first+last,by omega⟩) (ih (by omega) value)

variable (hash : ByteArray → Id (Vector UInt8 32))

/-- Every selected counter recomputes exactly the selected WOTS codeword. -/
theorem findCounter_sound (seed : PkSeed) (key : OtsKey) (msg : Digest)
    (start fuel : Nat) (counter : UInt32) (code : Codeword)
    (found : Internal.findCounter hash seed key msg start fuel = some (counter,code)) :
    encode hash seed key msg counter = some code :=
  findFirst_sound UInt32.ofNat (encode hash seed key msg) fuel start counter code found

theorem chain_to_end (seed : PkSeed) (key : OtsKey) (chainIndex : Fin Constants.V)
    (digit : Fin Constants.CHAIN_LENGTH) (value : Digest) :
    chain hash seed key chainIndex digit.val (Constants.CHAIN_LENGTH-1-digit.val)
        (by have := digit.isLt; omega)
        (chain hash seed key chainIndex 0 digit.val (by simp) value) =
      chain hash seed key chainIndex 0 (Constants.CHAIN_LENGTH-1) (by decide) value := by
  have digitBound := digit.isLt
  have sum : digit.val+(Constants.CHAIN_LENGTH-1-digit.val) = Constants.CHAIN_LENGTH-1 := by omega
  unfold chain
  simpa only [Nat.zero_add,sum] using
    chain_append (chainStep hash seed key chainIndex) 0 digit.val
      (Constants.CHAIN_LENGTH-1-digit.val) (by omega) value

/-- An accepted codeword reveals precisely enough of each chain to recover the public leaf. -/
theorem otsLeaf_signed_code (seed : PkSeed) (prf : Prf Id) (key : OtsKey) (msg : Digest)
    (counter : UInt32) (code : Codeword)
    (encoded : encode hash seed key msg counter = some code) :
    otsLeaf hash seed key msg counter
      (Vector.ofFn fun i => chain hash seed key i 0 (code[i]).val (by simp) (prf (adrsPrf key i))) =
      some (otsPublicLeaf hash seed prf key) := by
  simp only [otsLeaf,encoded,otsPublicLeaf,chainStarts,RustCrypto.OrderedVector.ofFnInOrder_id,Bind.bind,Pure.pure]
  apply congrArg (fun ends => some (otsLeafHash hash seed key ends))
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn,Fin.getElem_fin]
  exact chain_to_end hash seed key ⟨i,hi⟩ code[i] (prf (adrsPrf key ⟨i,hi⟩))

/-- The bounded counter search and deterministic signing chain values always verify to their public leaf. -/
theorem otsLeaf_findCounter (seed : PkSeed) (prf : Prf Id) (key : OtsKey) (msg : Digest)
    (start fuel : Nat) (counter : UInt32) (code : Codeword)
    (found : Internal.findCounter hash seed key msg start fuel = some (counter,code)) :
    otsLeaf hash seed key msg counter
      (Vector.ofFn fun i => chain hash seed key i 0 (code[i]).val (by simp) (prf (adrsPrf key i))) =
      some (otsPublicLeaf hash seed prf key) :=
  otsLeaf_signed_code hash seed prf key msg counter code
    (findCounter_sound hash seed key msg start fuel counter code found)

open Aeneas Aeneas.Std
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib

/-- The source signing-value model, at every accepted counter, recovers its actual public leaf. -/
theorem otsLeaf_signatureValue (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : OtsKey) (msg : Digest) (start fuel : Nat) (counter : UInt32) (code : Codeword)
    (found : Internal.findCounter hashId (nativeNode seed) key msg start fuel = some (counter,code)) :
    otsLeaf hashId (nativeNode seed) key msg counter
      (Vector.ofFn (RustCrypto.WotsEthlib.signatureValue seed secret key code)) =
      some (otsPublicLeaf hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf hashId (nativeNode seed) (nativeSeed secret)) key) := by
  unfold RustCrypto.WotsEthlib.signatureValue
  exact otsLeaf_findCounter hashId (nativeNode seed)
    (EthLib.Cryptography.Sphincs.prf hashId (nativeNode seed) (nativeSeed secret))
    key msg start fuel counter code found


end RustCrypto.CanonicalCorrectness
