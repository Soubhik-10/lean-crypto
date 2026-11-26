module
public import RustCrypto.WotsSignSource
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Each actual source signing step reveals the canonical chain at its selected digit. -/
theorem sign_step_ethlib (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (digits : WotsSignSource.Digits) (chain : Fin EthLib.Cryptography.Sphincs.Constants.V)
    (digit : Fin EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH)
    (hdigit : (digits[chain.val]!).val = digit.val) (oldTag : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = typedKeyHead seed key oldTag old2 old3) :
    nativeNode (WotsSignSource.signStep address secret (stepWord key.leaf) digits chain.val).1 =
      EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) key chain 0 digit.val (by simp)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
          (nativeNode seed) (nativeSeed secret) (EthLib.Cryptography.Sphincs.adrsPrf key chain)) ∧
    ∃ word2 word3, (WotsSignSource.signStep address secret (stepWord key.leaf) digits chain.val).2.val.take 48 =
      keyHead seed key word2 word3 := by
  have hs := chain_start_model address seed secret key chain oldTag old2 old3 hhead
  have hb : 0+(digits[chain.val]!).val < EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH := by
    rw [Nat.zero_add,hdigit]
    exact digit.isLt
  have hw := walk_ethlib seed key chain (digits[chain.val]!).val 0 0 0
    (WotsSource.chainStart address secret (stepWord key.leaf) (stepWord chain.val)).2
    (WotsSource.chainStart address secret (stepWord key.leaf) (stepWord chain.val)).1 hs.2 hb
  constructor
  · simpa only [WotsSignSource.signStep, hdigit, hs.1] using hw.1
  · simpa only [WotsSignSource.signStep] using hw.2

theorem overwrite_layout {α : Type} (output node : List α) (offset : Nat)
    (hnode : node.length = 16) (hroom : offset+16 ≤ output.length) :
    output.setSlice! offset node = output.take offset ++ node ++ output.drop (offset+16) := by
  have hm : min node.length (output.length-offset) = 16 := by omega
  simp only [List.setSlice!,hm]
  have ht : node.take 16 = node := List.take_of_length_le (by omega)
  rw [ht]

theorem overwrite_take {α : Type} (output node : List α) (offset : Nat)
    (hnode : node.length = 16) (hroom : offset+16 ≤ output.length) :
    (output.setSlice! offset node).take (offset+16) = output.take offset ++ node := by
  rw [overwrite_layout output node offset hnode hroom]
  have hp : offset ≤ output.length := by omega
  simp [List.take_append, List.take_of_length_le, hnode, Nat.min_eq_left hp]

theorem overwrite_drop {α : Type} (output node : List α) (offset extra : Nat)
    (hnode : node.length = 16) (hroom : offset+16 ≤ output.length) :
    (output.setSlice! offset node).drop (offset+16+extra) = output.drop (offset+16+extra) := by
  rw [overwrite_layout output node offset hnode hroom]
  have hp : offset ≤ output.length := by omega
  simp [List.drop_append, hnode, Nat.min_eq_left hp, List.drop_drop,
    Nat.add_comm, Nat.add_left_comm]

@[irreducible] def signatureValue (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (code : EthLib.Cryptography.Sphincs.Codeword)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) : EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key chain 0 (code[chain]).val
    (by simp) (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId
      (nativeNode seed) (nativeSeed secret) (EthLib.Cryptography.Sphincs.adrsPrf key chain))

@[irreducible] def signatureBytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (code : EthLib.Cryptography.Sphincs.Codeword)
    (start fuel : Nat) : List UInt8 :=
  (((List.ofFn (signatureValue seed secret key code)).drop start).take fuel).flatMap Vector.toList

theorem signature_bytes_zero (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (code : EthLib.Cryptography.Sphincs.Codeword) (start : Nat) :
    signatureBytes seed secret key code start 0 = [] := by simp [signatureBytes]

theorem signature_bytes_succ (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (code : EthLib.Cryptography.Sphincs.Codeword)
    (start fuel : Nat) (hstart : start < EthLib.Cryptography.Sphincs.Constants.V) :
    signatureBytes seed secret key code start (fuel+1) =
      (signatureValue seed secret key code ⟨start,hstart⟩).toList ++
        signatureBytes seed secret key code (start+1) fuel := by
  unfold signatureBytes
  rw [List.drop_eq_getElem_cons (by simpa using hstart)]
  simp only [List.take_succ_cons, List.flatMap_cons, List.getElem_ofFn]

/-- All source signing iterations serialize exactly the canonical WOTS values and retain surrounding bytes. -/
theorem sign_collect_ethlib (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (digits : WotsSignSource.Digits)
    (code : EthLib.Cryptography.Sphincs.Codeword)
    (hdigits : ∀ i : Fin EthLib.Cryptography.Sphincs.Constants.V, (digits[i.val]!).val = (code[i]).val)
    (fuel : Nat) :
    ∀ (start : Nat) (address : Address) (output : List U8) (oldTag : U32) (old2 old3 : Nat),
      address.val.take 48 = typedKeyHead seed key oldTag old2 old3 →
      1028 ≤ output.length → start+fuel ≤ EthLib.Cryptography.Sphincs.Constants.V →
    (WotsSignSource.signCollect secret (stepWord key.leaf) digits fuel start address output).2.map
        (fun b => UInt8.ofBitVec b.bv) =
      (output.map (fun b => UInt8.ofBitVec b.bv)).take (4+start*16) ++
        signatureBytes seed secret key code start fuel ++
        (output.map (fun b => UInt8.ofBitVec b.bv)).drop (4+(start+fuel)*16) ∧
    ∃ tag word2 word3,
      (WotsSignSource.signCollect secret (stepWord key.leaf) digits fuel start address output).1.val.take 48 =
        typedKeyHead seed key tag word2 word3 := by
  induction fuel with
  | zero =>
    intro start address output oldTag old2 old3 hhead hout hbound
    constructor
    · simp only [WotsSignSource.signCollect, signature_bytes_zero, Nat.add_zero, List.append_nil,
        List.take_append_drop]
    · exact ⟨oldTag,old2,old3,by simpa only [WotsSignSource.signCollect] using hhead⟩
  | succ fuel ih =>
    intro start address output oldTag old2 old3 hhead hout hbound
    have hstart : start < EthLib.Cryptography.Sphincs.Constants.V := by omega
    have hv : EthLib.Cryptography.Sphincs.Constants.V = 64 := by rfl
    have hs := sign_step_ethlib address seed secret key digits ⟨start,hstart⟩
      (code[(⟨start,hstart⟩ : Fin EthLib.Cryptography.Sphincs.Constants.V)]) (hdigits ⟨start,hstart⟩) oldTag old2 old3 hhead
    have hsvalue : nativeNode (WotsSignSource.signStep address secret (stepWord key.leaf) digits start).1 =
        signatureValue seed secret key code ⟨start,hstart⟩ := by
      simpa only [signatureValue] using hs.1
    simp only [WotsSignSource.signCollect]
    generalize hx : WotsSignSource.signStep address secret (stepWord key.leaf) digits start = next at hs hsvalue ⊢
    obtain ⟨word2,word3,hframe⟩ := hs.2
    have hr := ih (start+1) next.2 (output.setSlice! (4+start*16) next.1.val)
      0#u32 word2 word3 hframe (by simpa only [List.length_setSlice!] using hout) (by omega)
    have hn := congrArg Vector.toList hsvalue
    rw [native_node_list] at hn
    constructor
    · rw [hr.1]
      simp only [List.map_setSlice!]
      have hnode : (next.1.val.map (fun b => UInt8.ofBitVec b.bv)).length = 16 := by simp
      have hroom : (4+start*16)+16 ≤ (output.map (fun b => UInt8.ofBitVec b.bv)).length := by
        simp only [List.length_map]
        omega
      have hcut : 4+(start+1)*16 = (4+start*16)+16 := by omega
      have htail : 4+(start+1+fuel)*16 = (4+start*16)+16+fuel*16 := by omega
      have hfinal : 4+(start+(fuel+1))*16 = (4+start*16)+16+fuel*16 := by omega
      rw [hcut,htail,hfinal,overwrite_take _ _ _ hnode hroom,overwrite_drop _ _ _ _ hnode hroom,
        hn,signature_bytes_succ seed secret key code start fuel hstart]
      simp only [List.append_assoc]
    · exact hr.2

end RustCrypto.WotsEthlib
