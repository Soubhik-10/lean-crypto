module
public import RustCrypto.Wots.Encoding.SearchBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem overwrite_layout_any {α : Type} (output node : List α) (offset : Nat)
    (hroom : offset+node.length ≤ output.length) :
    output.setSlice! offset node = output.take offset ++ node ++ output.drop (offset+node.length) := by
  have hm : min node.length (output.length-offset) = node.length := Nat.min_eq_left (by omega)
  simp only [List.setSlice!,hm,List.take_length]

theorem counter_header (output : List U8) (counter : U32) (hout : 1028 ≤ output.length) :
    ((output.setSlice! 0 (core.num.U32.to_be_bytes counter).val).map
      (fun b => UInt8.ofBitVec b.bv)).take 4 =
        (core.num.U32.to_be_bytes counter).val.map (fun b => UInt8.ofBitVec b.bv) ∧
    ((output.setSlice! 0 (core.num.U32.to_be_bytes counter).val).map
      (fun b => UInt8.ofBitVec b.bv)).drop 1028 = (output.map (fun b => UInt8.ofBitVec b.bv)).drop 1028 := by
  let before := output.map (fun b => UInt8.ofBitVec b.bv)
  let header := (core.num.U32.to_be_bytes counter).val.map (fun b => UInt8.ofBitVec b.bv)
  have hlen : header.length = 4 := by simp [header]
  have hroom : 0+header.length ≤ before.length := by simp only [before,List.length_map]; omega
  have hwrite := overwrite_layout_any before header 0 hroom
  simp only [List.take_zero,List.nil_append,Nat.zero_add,hlen] at hwrite
  simp only [List.map_setSlice!]
  change (before.setSlice! 0 header).take 4 = header ∧
    (before.setSlice! 0 header).drop 1028 = before.drop 1028
  rw [hwrite]
  have ht : header.take 4 = header := List.take_of_length_le (by omega)
  have hd : header.drop 1028 = [] := List.drop_eq_nil_of_le (by omega)
  simp only [List.take_append,List.drop_append,hlen,ht,hd,Nat.sub_self,List.take_zero,List.append_nil,
    List.nil_append,List.drop_drop,Nat.reduceSub,Nat.reduceAdd]
  trivial

theorem complete_signature_bytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (code : EthLib.Cryptography.Sphincs.Codeword) :
    signatureBytes seed secret key code 0 64 =
      (EthLib.Cryptography.Sphincs.packDigests (Vector.ofFn (signatureValue seed secret key code))).data.toList := by
  simp only [EthLib.Cryptography.Sphincs.packDigests,EthLib.Base.packBytes,
    OrderedVector.flatten_list,Vector.toList_ofFn]
  unfold signatureBytes
  simp only [List.drop_zero]
  have hlen : (List.ofFn (signatureValue seed secret key code)).length = EthLib.Cryptography.Sphincs.Constants.V :=
    List.length_ofFn
  have hle : (List.ofFn (signatureValue seed secret key code)).length ≤ 64 :=
    Nat.le_of_eq (hlen.trans (by rfl))
  rw [List.take_of_length_le hle]

@[irreducible] def signingResult
    (choice : Option (UInt32 × EthLib.Cryptography.Sphincs.Codeword))
    (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (original : Slice U8) (out : Option Unit × Address × Slice U8) : Prop :=
  match choice with
  | none => out.1 = none ∧ out.2.2 = original ∧ out.2.1.val.take 48 = typedKeyHead seed key 7#u32 0 0
  | some (counter,code) => out.1 = some () ∧
      out.2.2.val.map (fun b => UInt8.ofBitVec b.bv) =
        (EthLib.Cryptography.Sphincs.toByte EthLib.Cryptography.Sphincs.Constants.COUNTER_LEN counter.toNat).toArray.toList ++
          (EthLib.Cryptography.Sphincs.packDigests (Vector.ofFn (signatureValue seed secret key code))).data.toList ++
          (original.val.map (fun b => UInt8.ofBitVec b.bv)).drop 1028 ∧
      ∃ tag word2 word3, out.2.1.val.take 48 = typedKeyHead seed key tag word2 word3

/-- Complete bounded source WOTS signing agrees with canonical counter selection and serialized chain values. -/
@[step] theorem sign_any_pair_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (message : Node) (output : Slice U8) (limit : U64) (oldTag oldPair : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = headBytes seed (stepWord key.layer.toNat) (treeWord key.tree)
      oldTag oldPair (stepWord old2) (stepWord old3))
    (hsize : 1028 ≤ output.val.length) :
    lean_sphincs.wots.sign address secret (stepWord key.leaf) message output limit ⦃ out =>
      signingResult (EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) key (nativeNode message) 0 limit.val) seed secret key output out ⦄ := by
  let initial := WotsSource.domain address 7#u32 (stepWord key.leaf)
  have hzero : stepWord 0 = 0#u32 := by
    apply UScalar.eq_of_val_eq
    rfl
  have hi : initial.val.take 48 = typedKeyHead seed key 7#u32 0 0 := by
    simpa only [initial,typedKeyHead,hzero] using
      domain_frame address seed (stepWord key.layer.toNat) (treeWord key.tree) oldTag
        oldPair (stepWord old2) (stepWord old3) 7#u32 (stepWord key.leaf) hhead
  have hp : (initial.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList := by
    rw [hi]
    exact enc_head_native seed key
  have hs := search_ethlib (initial.val.take 48) message (nativeNode seed) key hp limit.val 0
  apply WP.spec_mono (WotsSignSource.sign_spec address secret (stepWord key.leaf) message output limit hsize)
  intro out hout
  generalize hsource : CounterSearch.search (initial.val.take 48) message 0 limit.val = source at hs
  dsimp only at hout
  dsimp only [initial] at hsource
  rw [hsource] at hout
  generalize hreference : EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
    (nativeNode seed) key (nativeNode message) 0 limit.val = reference at hs ⊢
  cases source with
  | none =>
    cases reference with
    | none =>
      simp only [signingResult]
      dsimp only at hout
      exact ⟨hout.1,hout.2.1,hout.2.2.trans hi⟩
    | some value => simp only [searchChoice] at hs
  | some sourceValue =>
    rcases sourceValue with ⟨counter,digits⟩
    cases reference with
    | none => simp only [searchChoice] at hs
    | some referenceValue =>
      rcases referenceValue with ⟨refCounter,code⟩
      simp only [searchChoice] at hs
      dsimp only at hout
      rcases hout with ⟨hresult,searched,hsearchHead,hcollect⟩
      have hc := sign_collect_ethlib seed secret key digits code hs.2 64 0 searched
        (output.val.setSlice! 0 (core.num.U32.to_be_bytes counter).val) 7#u32 0 0
        (hsearchHead.trans hi) (by simpa only [List.length_setSlice!] using hsize)
        (Nat.le_of_eq (by rfl))
      rw [← hcollect] at hc
      dsimp only at hc
      have hb := counter_header output.val counter hsize
      have hcounter := counter_bytes_native counter
      rw [hs.1] at hcounter
      simp only [signingResult]
      refine ⟨hresult,?_,hc.2⟩
      simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.reduceMul,Nat.reduceAdd,
        hb.1,hb.2,← hcounter,complete_signature_bytes] using hc.1


@[step] theorem sign_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (message : Node) (output : Slice U8) (limit : U64) (oldTag : U32) (old2 old3 : Nat)
    (hhead : address.val.take 48 = typedKeyHead seed key oldTag old2 old3)
    (hsize : 1028 ≤ output.val.length) :
    lean_sphincs.wots.sign address secret (stepWord key.leaf) message output limit ⦃ out =>
      signingResult (EthLib.Cryptography.Sphincs.Internal.findCounter EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) key (nativeNode message) 0 limit.val) seed secret key output out ⦄ := by
  exact sign_any_pair_ethlib_spec address seed secret key message output limit oldTag (stepWord key.leaf) old2 old3 hhead hsize

end RustCrypto.WotsEthlib
