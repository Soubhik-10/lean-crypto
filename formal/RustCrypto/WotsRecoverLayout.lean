module
public import RustCrypto.WotsRecoverModel
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

theorem digit_relation_of_values (digits : Digits) (word : EthLib.Cryptography.Sphincs.Codeword)
    (hvalues : digits.val.map UScalar.val = word.toList.map Fin.val) : digitRelation digits word := by
  intro chain
  have hsource : chain.val < digits.val.length := by
    have hc : chain.val < 64 := chain.isLt
    scalar_tac
  have hword : chain.val < word.toList.length := by
    simpa only [Vector.length_toList] using chain.isLt
  have h := congrArg (fun values : List Nat => values[chain.val]!) hvalues
  rw [getElem!_pos _ chain.val (by simp only [List.length_map]; exact hsource),
    getElem!_pos _ chain.val (by simp only [List.length_map]; exact hword)] at h
  simp only [List.getElem_map,Vector.getElem_toList] at h
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos digits.val chain.val hsource]
  exact h

theorem ends_before_succ (bytes : List U8) (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (count : Nat) (hcount : count < 64) :
    endsBefore bytes word seed key (count+1) = endsBefore bytes word seed key count ++
      (endValue seed key word ⟨count,by simpa only [EthLib.Cryptography.Sphincs.Constants.V] using hcount⟩
        (nativeNode (ForsRead.nodeAt bytes (16*count)))).toList := by
  unfold endsBefore
  rw [OrderedPrefix.prefix_succ (endVector bytes word seed key) Vector.toList count
    (by simpa only [EthLib.Cryptography.Sphincs.Constants.V] using hcount)]
  simp only [endVector,Vector.getElem_ofFn]

end RustCrypto.WotsRecover
