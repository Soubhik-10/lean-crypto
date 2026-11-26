module
public import RustCrypto.WotsBackend
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem key_frame_tree (address : Address) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (kind : EthLib.Cryptography.Sphincs.AdrsType) (hframe : keyFrame address seed key kind) :
    TreePrimitives.frame address seed key.layer key.tree := by
  rcases hframe with ⟨word2,word3,hhead⟩
  exact ⟨addressTag kind,stepWord key.leaf,word2,word3,hhead⟩

/-- Backend-independent composition; concrete source backends must supply `ChainsContract`. -/
theorem entry_with_backend (unit : Nat) (hbackend : ChainsContract unit)
    (address : Address) (reader : Slice U8) (message seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hframe : TreePrimitives.frame address seed key.layer key.tree) :
    lean_sphincs.wots.recover_wots address reader (stepWord key.leaf) message ⦃ out =>
      out.1.map nativeNode = expectedLeaf reader.val seed key message ∧
      TreePrimitives.frame out.2.1 seed key.layer key.tree ∧
      out.2.2.val = reader.val.drop (consumed unit reader.val seed key message) ⦄ := by
  unfold lean_sphincs.wots.recover_wots
  simp only [lean_sphincs.wots.WOTS_ENCODING,lean_sphincs.wots.WOTS_PUBLIC_KEY,lean_sphincs.wots.WOTS_CHAIN]
  step with ForsPrimitives.domain_frame_spec address seed key.layer key.tree 7#u32 (stepWord key.leaf) hframe
    as ⟨encodingAddress,hencodingHead⟩
  have hencodingFrame : TreePrimitives.frame encodingAddress seed key.layer key.tree :=
    ⟨7#u32,stepWord key.leaf,0#u32,0#u32,hencodingHead⟩
  have h4 : (4#usize).val = 4 := rfl
  by_cases hshort : reader.val.length < 4
  · rw [RustParser.take_failure 4#usize reader hshort]
    simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
    refine ⟨?_,hencodingFrame,?_⟩
    · have hn : ¬1028 ≤ reader.val.length := by omega
      simp only [expectedLeaf,ite_eq_right hn,Option.map_none]
    · simp only [consumed,ite_eq_left hshort,List.drop_zero]
  · have hread : (4#usize).val ≤ reader.val.length := by scalar_tac
    rw [RustParser.take_success 4#usize reader hread]
    simp only [Aeneas.Std.uncurry,bind_ok,core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    have hcounter : RustParser.readPrefix 4#usize reader hread = counterBytes reader.val := by
      apply Aeneas.Std.Array.ext
      rw [counterBytes_val reader.val (by omega)]
      simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,h4]
    rw [hcounter]
    have hzero : stepWord 0 = 0#u32 := rfl
    have hencodingPrefix : (encodingAddress.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
        (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsEnc key).toList := by
      rw [hencodingHead]
      simpa only [typedKeyHead,hzero] using enc_head_native seed key
    step with encode_counter_spec encodingAddress (counterBytes reader.val) message seed key hencodingPrefix
      as ⟨code,encodedAddress,hcode,hencoded⟩
    have hencode : EthLib.Cryptography.Sphincs.codeword? (nativeNode code) = encoding reader.val seed key message := hcode
    have hencodedFrame : TreePrimitives.frame encodedAddress seed key.layer key.tree :=
      ⟨7#u32,stepWord key.leaf,0#u32,0#u32,hencoded.trans hencodingHead⟩
    step with codeword_native_spec code as ⟨sourceWord,hword⟩
    rw [hencode] at hword
    cases sourceWord with
    | none =>
      cases href : encoding reader.val seed key message with
      | some word =>
        simp only [href,Option.map_none,Option.map_some] at hword
        cases hword
      | none =>
        simp only [bind_ok,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
        refine ⟨?_,hencodedFrame,?_⟩
        · rw [no_encoding_leaf reader.val seed key message href]
          rfl
        · simp only [consumed,ite_eq_right hshort,href,Option.isNone_none,ite_true,
            RustParser.readSuffix,Slice.from_val,h4]
    | some digits =>
      cases href : encoding reader.val seed key message with
      | none =>
        simp only [href,Option.map_some,Option.map_none] at hword
        cases hword
      | some word =>
        have hvalues : digits.val.map UScalar.val = word.toList.map Fin.val := by
          simpa only [href,Option.map_some,Option.some.injEq] using hword
        have hdigits := digit_relation_of_values digits word hvalues
        step with ForsPrimitives.domain_frame_spec encodedAddress seed key.layer key.tree 1#u32 (stepWord key.leaf) hencodedFrame
          as ⟨publicAddress,hpublic⟩
        step with accumulator_spec publicAddress as ⟨ends,hends⟩
        have hpublicFrame : TreePrimitives.frame publicAddress seed key.layer key.tree :=
          ⟨1#u32,stepWord key.leaf,0#u32,0#u32,hpublic⟩
        step with ForsPrimitives.domain_frame_spec publicAddress seed key.layer key.tree 0#u32 (stepWord key.leaf) hpublicFrame
          as ⟨chainAddress,hchainHead⟩
        have hchainFrame : keyFrame chainAddress seed key .wotsHash := by
          refine ⟨0#u32,0#u32,?_⟩
          have htag : addressTag .wotsHash = 0#u32 := rfl
          simpa only [htag] using hchainHead
        step with hbackend chainAddress (RustParser.readSuffix 4#usize reader) ends digits word seed key hdigits hchainFrame
          as ⟨status,nextAddress,remaining,nextEnds,hstatus,hnextFrame,hremaining,hendBytes⟩
        have htail : (RustParser.readSuffix 4#usize reader).val.length = reader.val.length-4 := by
          simp only [RustParser.readSuffix,Slice.from_val,h4,List.length_drop]
        by_cases hroom : 1028 ≤ reader.val.length
        · have hroomTail : 1024 ≤ (RustParser.readSuffix 4#usize reader).val.length := by omega
          rw [ite_eq_left hroomTail] at hstatus hremaining
          rw [hstatus]
          have hp : nativeBytes (publicAddress.val.take 48) =
              (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsPk key).toList := by
            rw [hpublic]
            simpa only [nativeBytes,typedKeyHead,hzero] using pk_head_native seed key
          have hinput : RustCrypto.bytes nextEnds = EthLib.Cryptography.Sphincs.thInput (nativeNode seed)
              (EthLib.Cryptography.Sphincs.adrsPk key) (EthLib.Cryptography.Sphincs.packDigests
                (endVector (reader.val.drop 4) word seed key)) := by
            apply ByteArray.ext
            apply _root_.Array.toList_inj.1
            rw [source_bytes_list]
            change nativeBytes nextEnds = _
            rw [hendBytes hroomTail,hends,hp,ends_full]
            simp only [RustParser.readSuffix,Slice.from_val,h4,EthLib.Cryptography.Sphincs.thInput,EthLib.Base.packBytes,
              ByteArray.data_append,Array.toList_append,List.append_assoc]
            rfl
          simp only [alloy_primitives.utils.Keccak256.finalize]
          step with truncate_spec (RustCrypto.digest nextEnds) as ⟨root,hroot⟩
          refine ⟨?_,key_frame_tree nextAddress seed key .wotsHash hnextFrame,?_⟩
          · rw [encoding_leaf reader.val seed key message word hroom href]
            change some (nativeNode root) = some _
            apply congrArg some
            apply Vector.toList_inj.1
            rw [native_node_list,hroot,List.map_take,ByteBridge.digest_native,
              EthLib.Cryptography.Sphincs.otsLeafHash,th_pure_list,hinput]
          · rw [hremaining]
            simp only [RustParser.readSuffix,Slice.from_val,h4,List.drop_drop,consumed,ite_eq_right hshort,
              href,Option.isNone_some,Bool.false_eq_true,ite_false,ite_eq_left hroom]
        · have hshortTail : ¬1024 ≤ (RustParser.readSuffix 4#usize reader).val.length := by omega
          rw [ite_eq_right hshortTail] at hstatus hremaining
          rw [hstatus]
          simp only [bind_ok,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok]
          refine ⟨?_,key_frame_tree nextAddress seed key .wotsHash hnextFrame,?_⟩
          · simp only [expectedLeaf,ite_eq_right hroom,Option.map_none]
          · rw [hremaining]
            simp only [RustParser.readSuffix,Slice.from_val,h4,List.drop_drop,List.length_drop,
              consumed,ite_eq_right hshort,href,Option.isNone_some,Bool.false_eq_true,ite_false,ite_eq_right hroom]

end RustCrypto.WotsRecover
