module
public import RustCrypto.WholeVerifyIndex
public import RustCrypto.WholeVerifyApi
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.AddressBridge
set_option maxHeartbeats 50000
set_option maxRecDepth 8192
attribute [local irreducible] EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.forsRecover EthLib.Cryptography.Sphincs.layerRoot

theorem initial_seed (key : Aeneas.Std.Array U8 32#usize) :
    key.val.take 16 = (MessageHashBridge.keySeed key).val := by
  unfold MessageHashBridge.keySeed
  rw [ForsRead.nodeAt_val key.val 0 (by scalar_tac)]
  rfl

theorem prefix_rho (reader : Slice U8) (hroom : (16#usize).val ≤ reader.val.length) :
    RustParser.readPrefix 16#usize reader hroom = ForsRead.nodeAt reader.val 0 := by
  apply Aeneas.Std.Array.ext
  rw [ForsRead.nodeAt_val reader.val 0 hroom]
  simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,List.drop_zero]
  rfl

theorem mask_shift : ((1#u32 <<< 18#i32) : Result U32) = .ok 262144#u32 := by rfl

theorem mask_sub : ((262144#u32 - 1#u32) : Result U32) = .ok 262143#u32 := by rfl

/-- Complete source recovery with independently discharged source backends. -/
theorem recover_root_with_backends (unit : Nat) (wots : WotsRecover.ChainsContract unit)
    (fors : ForsContract) : RootContract := by
  intro key message bytes hsize
  have hr : (16#usize).val ≤ bytes.val.length := by change 16 ≤ bytes.val.length; omega
  unfold lean_sphincs.verifier.recover_root
  simp only [lean_sphincs.signature.Reader.new,bind_ok,RustParser.take_success 16#usize bytes hr,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  rw [prefix_rho bytes hr]
  step with MessageHashBridge.message_digest_bytes_ethlib_spec key message (ForsRead.nodeAt bytes.val 0)
    as ⟨digest,hdigest⟩
  rw [read_array_eq digest 30#usize (by scalar_tac),read_array_eq digest 31#usize (by scalar_tac),
    read_array_eq digest 32#usize (by scalar_tac)]
  simp only [bind_ok,lift,mask_shift,mask_sub]
  rw [read_array_eq digest 33#usize (by scalar_tac)]
  simp only [bind_ok]
  simp only [Aeneas.Std.Array.getElem!_Nat_eq]
  generalize htdef : (core.num.U32.from_be_bytes (Aeneas.Std.Array.make 4#usize
    [0#u8,digest.val[(30#usize).val]!,digest.val[(31#usize).val]!,digest.val[(32#usize).val]!]) &&& 262143#u32) = tree
  generalize hldef : digest.val[(33#usize).val]! = leaf
  have ht : tree.val = MessageHashBridge.rawTree digest := by
    rw [←htdef]
    exact MessageHashBridge.masked_tree_val digest
  have hl : leaf.val = MessageHashBridge.rawLeaf digest := by rw [←hldef]; rfl
  have htb : tree.val < 262144 := by rw [ht]; exact MessageHashBridge.raw_tree_bound digest
  step as ⟨shifted,hshifted⟩
  have hs : shifted.val = tree.val*256 := by
    norm_num [Nat.shiftLeft_eq,U32.size,U32.numBits,UScalarTy.numBits] at hshifted
    omega
  let sourceIndex := core.convert.num.FromU64U32.from (shifted ||| core.convert.num.FromU32U8.from leaf)
  let index := EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest)
  have hindex : sourceIndex.val = index := by
    change (shifted ||| core.convert.num.FromU32U8.from leaf).val = index
    rw [UScalar.val_or,hs,core.convert.num.FromU32U8.from_val_eq]
    rw [Nat.mul_comm tree.val 256,←Nat.two_pow_add_eq_or_of_lt (show leaf.val < 2^8 by scalar_tac) tree.val]
    change 256*tree.val+leaf.val = index
    rw [ht,hl]
    simpa only [index,Nat.mul_comm] using (MessageHashBridge.digest_index_native digest).symm
  let seed := MessageHashBridge.keySeed key
  step with ContextFrame.context_frame_spec key seed (initial_seed key) as ⟨address,haddress⟩
  have htreeWord : core.convert.num.FromU64U32.from tree = treeWord
      (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromU64U32.from_val_eq,ht,digest_bottom_tree]
    change MessageHashBridge.rawTree digest = MessageHashBridge.rawTree digest%18446744073709551616
    rw [Nat.mod_eq_of_lt (by have hh := MessageHashBridge.raw_tree_bound digest; omega)]
  rw [htreeWord]
  have hset := ContextFrame.set_tree_frame_spec address seed .bottom .bottom 0
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree haddress
  have hz : stepWord EthLib.Cryptography.Sphincs.Layer.bottom.toNat = 0#u32 := rfl
  rw [hz] at hset
  step with hset as ⟨forsAddress,hforsAddress⟩
  have hleafWord : core.convert.num.FromU32U8.from leaf =
      stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).leaf := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromU32U8.from_val_eq,hl,digest_bottom_leaf]
    change MessageHashBridge.rawLeaf digest = MessageHashBridge.rawLeaf digest%4294967296
    rw [Nat.mod_eq_of_lt (by have hh := MessageHashBridge.raw_leaf_bound digest; omega)]
  have hcall := fors forsAddress (RustParser.readSuffix 16#usize bytes) digest seed index hforsAddress
  rw [←hleafWord] at hcall
  step with hcall
    as ⟨forsOption,afterFors,forsReader,hfors,hforsFrame,hforsReader⟩
  have hforsRoom : 4224 ≤ (RustParser.readSuffix 16#usize bytes).val.length := by
    simp only [RustParser.readSuffix,Slice.from_val,List.length_drop]
    change 4224 ≤ bytes.val.length-16
    omega
  rw [ite_eq_left hforsRoom] at hfors
  cases forsOption with
  | none => simp only [Option.map_none] at hfors; contradiction
  | some forsNode =>
    have hreader0 : forsReader.val = bytes.val.drop 4240 := by
      have h := hforsReader (by rfl)
      simp only [RustParser.readSuffix,Slice.from_val,List.drop_drop] at h
      exact h
    have hreference := reference_from_digest (publicKey key) (nativeSeed message) (signature bytes.val)
      (ForsDigest.nativeDigest digest) hdigest.symm
    rw [hreference]
    simp only [signature,publicKey]
    simp only [Option.map_some] at hfors
    have hforsNative := Option.some.inj hfors
    have hreaderPrefix : (RustParser.readSuffix 16#usize bytes).val = bytes.val.drop 16 := by
      simp only [RustParser.readSuffix,Slice.from_val]
      rfl
    rw [hreaderPrefix] at hforsNative
    rw [←hforsNative]
    rw [bottom_height_eq]
    simp only [bind_ok]
    have hi0 : sourceIndex.val = index/2^EthLib.Cryptography.Sphincs.Layer.bottom.below := by
      simpa only [EthLib.Cryptography.Sphincs.Layer.below,Nat.pow_zero,Nat.div_one] using hindex
    have hroom0 : 1028+16*EthLib.Cryptography.Sphincs.Layer.bottom.height ≤ forsReader.val.length := by
      rw [hreader0,List.length_drop,hsize]
      decide
    have hbottom := LayerInput.recover_layer_with_backend unit wots afterFors forsReader sourceIndex seed forsNode
      .bottom .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree index hi0 hroom0 hforsFrame
    rw [hz] at hbottom
    step with hbottom as ⟨bottomOption,afterBottom,bottomReader,index1,hbottom,hbottomFrame,hindex1,hbottomReader⟩
    rw [hreader0] at hbottom
    unfold layerRoots
    rw [←hbottom]
    cases bottomOption with
    | none =>
      simp only [
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok,Option.map_none]
    | some bottomNode =>
      simp only [Option.map_some]
      have hreader1 : bottomReader.val = bytes.val.drop 5396 := by
        have h := hbottomReader (by rfl)
        rw [hreader0,List.drop_drop] at h
        exact h
      have hi1 : index1.val = index/2^EthLib.Cryptography.Sphincs.Layer.middle.below := by
        simpa only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,EthLib.Cryptography.Sphincs.Layer.below,
          EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT,
          Nat.shiftRight_eq_div_pow] using hindex1
      rw [middle_height_eq]
      simp only [bind_ok]
      have hroom1 : 1028+16*EthLib.Cryptography.Sphincs.Layer.middle.height ≤ bottomReader.val.length := by
        rw [hreader1,List.length_drop,hsize]
        decide
      have hmiddle := LayerInput.recover_layer_with_backend unit wots afterBottom bottomReader index1 seed bottomNode
        .middle .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom index).tree index hi1 hroom1 hbottomFrame
      have ho : stepWord EthLib.Cryptography.Sphincs.Layer.middle.toNat = 1#u32 := rfl
      rw [ho] at hmiddle
      step with hmiddle as ⟨middleOption,afterMiddle,middleReader,index2,hmiddle,hmiddleFrame,hindex2,hmiddleReader⟩
      rw [hreader1] at hmiddle
      rw [←hmiddle]
      cases middleOption with
      | none =>
        simp only [
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok,Option.map_none]
      | some middleNode =>
        simp only [Option.map_some]
        have hreader2 : middleReader.val = bytes.val.drop 6552 := by
          have h := hmiddleReader (by rfl)
          rw [hreader1,List.drop_drop] at h
          exact h
        have hi2 : index2.val = index/2^EthLib.Cryptography.Sphincs.Layer.top.below := by
          simpa only [EthLib.Cryptography.Sphincs.OtsKey.ofIndex,EthLib.Cryptography.Sphincs.Layer.below,
            EthLib.Cryptography.Sphincs.Layer.height,EthLib.Cryptography.Sphincs.Constants.LOWER_HEIGHT,
            Nat.shiftRight_eq_div_pow] using hindex2
        rw [top_height_eq]
        simp only [bind_ok]
        have hroom2 : 1028+16*EthLib.Cryptography.Sphincs.Layer.top.height ≤ middleReader.val.length := by
          rw [hreader2,List.length_drop,hsize]
          decide
        have htop := LayerInput.recover_layer_with_backend unit wots afterMiddle middleReader index2 seed middleNode
          .top .middle (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .middle index).tree index hi2 hroom2 hmiddleFrame
        have htword : stepWord EthLib.Cryptography.Sphincs.Layer.top.toNat = 2#u32 := rfl
        rw [htword] at htop
        step with htop as ⟨topOption,afterTop,topReader,index3,htop,htopFrame,hindex3,htopReader⟩
        rw [hreader2] at htop
        rw [←htop]
        cases topOption with
        | none =>
          simp only [
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,WP.spec_ok,Option.map_none]
        | some topNode =>
          simp only [Option.map_some]
          have hreader3 : topReader.val = [] := by
            have h := htopReader (by rfl)
            rw [hreader2,List.drop_drop] at h
            have he : bytes.val.drop 7740 = [] := List.drop_eq_nil_of_le (by omega)
            exact h.trans he
          rw [RustParser.is_empty_eq]
          simp only [hreader3,List.length_nil,decide_true,bind_ok,core.bool.Bool.then_some,WP.spec_ok]
          rfl


end RustCrypto.WholeVerifier
