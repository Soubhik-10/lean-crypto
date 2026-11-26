module
public import RustCrypto.EncodingBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def digitsAgree (source : WotsSignSource.Digits) (reference : EthLib.Cryptography.Sphincs.Codeword) : Prop :=
  ∀ i : Fin EthLib.Cryptography.Sphincs.Constants.V, (source[i.val]!).val = (reference[i]).val

@[irreducible] def digitChoice (source : Option WotsSignSource.Digits) (reference : Option EthLib.Cryptography.Sphincs.Codeword) : Prop :=
  match source,reference with
  | none,none => True
  | some source,some reference => digitsAgree source reference
  | _,_ => False

theorem expected_digits_agree (code : Node) :
    digitsAgree (Codeword.expectedDigits code) (EthLib.Cryptography.Sphincs.Internal.digits (nativeNode code)) := by
  intro i
  have hi : i.val < 64 := Nat.lt_of_lt_of_eq i.isLt (by rfl)
  have hs := Codeword.expected_digit code i.val hi
  have hr := Codeword.digit_ethlib code ⟨i.val,hi⟩
  rw [digest_adapter] at hr
  exact hs.trans hr

theorem encode_eq_th (seed : EthLib.Cryptography.Sphincs.PkSeed)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (message : EthLib.Cryptography.Sphincs.Digest) (counter : UInt32) :
    EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId seed key message counter =
      EthLib.Cryptography.Sphincs.codeword? (EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId
        seed (EthLib.Cryptography.Sphincs.adrsEnc key)
        (EthLib.Base.packBytes message ++ EthLib.Base.packBytes
          (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN counter.toNat))) := by rfl

set_option maxHeartbeats 100000 in
theorem codeword_choice (code : Node) :
    digitChoice (if Codeword.sumPrefix (Codeword.expectedDigits code) 64 = 128
      then some (Codeword.expectedDigits code) else none)
      (EthLib.Cryptography.Sphincs.codeword? (nativeNode code)) := by
  have hsum := Codeword.digit_sum_ethlib code
  rw [digest_adapter] at hsum
  unfold EthLib.Cryptography.Sphincs.codeword?
  dsimp only
  rcases Classical.em (Codeword.sumPrefix (Codeword.expectedDigits code) 64 = 128) with h | h
  · have hs : EthLib.Cryptography.Sphincs.Internal.digitSum
        (EthLib.Cryptography.Sphincs.Internal.digits (nativeNode code)) =
          EthLib.Cryptography.Sphincs.Constants.TARGET_SUM :=
      hsum.symm.trans (h.trans (by rfl))
    have hb : (EthLib.Cryptography.Sphincs.Internal.digitSum
        (EthLib.Cryptography.Sphincs.Internal.digits (nativeNode code)) ==
          EthLib.Cryptography.Sphincs.Constants.TARGET_SUM) = true := beq_iff_eq.mpr hs
    conv => arg 1; rw [ite_eq_left h]
    conv => arg 2; rw [ite_eq_left hb]
    simpa only [digitChoice] using expected_digits_agree code
  · have hs : ¬ EthLib.Cryptography.Sphincs.Internal.digitSum
        (EthLib.Cryptography.Sphincs.Internal.digits (nativeNode code)) =
          EthLib.Cryptography.Sphincs.Constants.TARGET_SUM := by
      intro hs
      exact h (hsum.trans (hs.trans (by rfl)))
    have hb : ¬ (EthLib.Cryptography.Sphincs.Internal.digitSum
        (EthLib.Cryptography.Sphincs.Internal.digits (nativeNode code)) ==
          EthLib.Cryptography.Sphincs.Constants.TARGET_SUM) = true := by
      intro hb
      exact hs (beq_iff_eq.mp hb)
    conv => arg 1; rw [ite_eq_right h]
    conv => arg 2; rw [ite_eq_right hb]
    simp only [digitChoice]

/-- Every actual source counter candidate has exactly EthLib's codeword decision and digits. -/
theorem accept_ethlib (headBytes : List U8) (message : Node) (counter : U32)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hprefix : headBytes.map (fun b => UInt8.ofBitVec b.bv) =
      seed.toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList) :
    digitChoice (CounterSearch.accept headBytes message counter)
      (EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId seed key
        (nativeNode message) (UInt32.ofBitVec counter.bv)) := by
  let code := CounterSearch.encoded headBytes message (core.num.U32.to_be_bytes counter)
  have he : EthLib.Cryptography.Sphincs.encode EthLib.Cryptography.Sphincs.hashId seed key
      (nativeNode message) (UInt32.ofBitVec counter.bv) =
        EthLib.Cryptography.Sphincs.codeword? (nativeNode code) := by
    rw [encode_eq_th, ← encoded_native headBytes message counter seed key hprefix]
  rw [he]
  simpa only [CounterSearch.accept] using codeword_choice code

end RustCrypto.WotsEthlib
