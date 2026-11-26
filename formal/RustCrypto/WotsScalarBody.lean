module
public import RustCrypto.WotsRecoverModel
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem scalar_body_spec (address : Address) (reader : Slice U8) (ends : List U8) (digits : Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (index : Usize)
    (hindex : index.val < 64) (hreader : 16 ≤ reader.val.length) (hdigits : digitRelation digits word)
    (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop.body digits address reader ends index ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextReader,nextEnds,nextIndex) =>
          nextIndex.val = index.val+1 ∧ nextReader.val = reader.val.drop 16 ∧ keyFrame nextAddress seed key .wotsHash ∧
          ∃ root : Node, nativeNode root = endValue seed key word
            ⟨index.val,by simpa only [EthLib.Cryptography.Sphincs.Constants.V] using hindex⟩
            (nativeNode (ForsRead.nodeAt reader.val 0)) ∧ nextEnds = ends ++ root.val ⦄ := by
  let chain : Fin EthLib.Cryptography.Sphincs.Constants.V := ⟨index.val,hindex⟩
  unfold lean_sphincs.wots.recover_chains_loop.body
  have hrun : index < lean_sphincs.params.WOTS_CHAINS := by
    simp only [lean_sphincs.params.WOTS_CHAINS]
    scalar_tac
  simp only [ite_eq_left hrun]
  rw [RustParser.take_success 16#usize reader hreader]
  simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    alloy_primitives.bits.fixed.FixedBytes.new]
  step as ⟨chainWord,hchainWord⟩
  step as ⟨digit,hdigit⟩
  have hc : chainWord = stepWord index.val := by
    apply UScalar.eq_of_val_eq
    change chainWord.val = index.val%4294967296
    have hb : index.val < 4294967296 := by omega
    rw [Nat.mod_eq_of_lt hb]
    scalar_tac
  rw [hc]
  have hd : digit.val = (word[chain]).val := by
    have he : digit = digits[index.val]! := by
      rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos digits.val index.val (by scalar_tac)]
      exact hdigit
    rw [he]
    exact hdigits chain
  have hs : RustParser.readPrefix 16#usize reader hreader = ForsRead.nodeAt reader.val 0 := by
    apply Aeneas.Std.Array.ext
    rw [ForsRead.nodeAt_val reader.val 0 (by omega)]
    have h16 : (16#usize).val = 16 := rfl
    simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,List.drop_zero,h16]
  rw [hs]
  simp only [lean_sphincs.params.CHAIN_END]
  step with walk_end_spec address seed key word chain digit (ForsRead.nodeAt reader.val 0) hd hframe
    as ⟨root,nextAddress,hroot,hnextFrame⟩
  simp only [alloy_primitives.utils.Keccak256.update,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreConvertAsRefSliceU8.as_ref,Aeneas.Std.Array.to_slice]
  step as ⟨nextIndex,hnextIndex⟩
  refine ⟨?_,?_,hnextFrame,root,hroot,?_⟩
  · have h1 : (1#usize).val = 1 := rfl
    simpa only [h1] using hnextIndex
  · have h16 : (16#usize).val = 16 := rfl
    simp only [RustParser.readSuffix,Slice.from_val,h16]
  · simp only [Slice.from_val]

end RustCrypto.WotsRecover
