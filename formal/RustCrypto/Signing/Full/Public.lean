module
public import RustCrypto.Signing.Full.Index
public import RustCrypto.Tree.Cache.New
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[irreducible] def publicRefinement (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64)
    (out : core.result.Result (Aeneas.Std.Array U8 7740#usize) lean_sphincs.signing.SignError) : Prop :=
  ∃ (seed rho : Node) (digest : Aeneas.Std.Array U8 34#usize),
    nativeNode seed = KeyMaterial.publicSeed (nativeSeed secret) ∧
    nativeNode rho = EthLib.Cryptography.Sphincs.prfMsg EthLib.Cryptography.Sphincs.hashId
      (KeyMaterial.secretPrf (nativeSeed secret)) (KeyMaterial.publicSeed (nativeSeed secret)) (nativeSeed message) ∧
    ForsDigest.nativeDigest digest = EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.hashId
      (nativeNode rho) (nativeNode seed) (KeyGen.publicKey (nativeSeed secret)).root (nativeSeed message) ∧
    nativeResult out = signFromDigest seed secret digest rho limit.val

@[step] theorem sign_with_limit_refinement (secret message : Aeneas.Std.Array U8 32#usize) (limit : U64) :
    lean_sphincs.signing.sign_with_limit secret message limit ⦃ out => publicRefinement secret message limit out ⦄ := by
  unfold lean_sphincs.signing.sign_with_limit
  step with KeyMaterial.expand_key_ethlib_spec secret as ⟨seed,skPrf,hseed,hskPrf⟩
  simp only [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndexMut.index_mut,
    alloy_primitives.bits.fixed.FixedBytes.as_slice,lean_sphincs.params.NODE_BYTES,
    lean_sphincs.core.ops.index.IndexMutArray,Aeneas.Std.core.ops.index.IndexMutArray]
  step as ⟨head,restoreHead,hhead,hlen,hrestoreHead⟩
  step as ⟨copiedSeed,hcopiedSeed⟩
  have hseedPrefix : (restoreHead copiedSeed).val.take 16 = seed.val := by
    rw [hrestoreHead,hcopiedSeed]
    simp [List.setSlice!,Aeneas.Std.Array.repeat_val,Aeneas.Std.Array.to_slice,List.take_of_length_le]
  step with ContextFrame.context_frame_spec (restoreHead copiedSeed) seed hseedPrefix as ⟨address,haddress⟩
  step with TopCache.new_ethlib_spec address seed secret .bottom 0 haddress as ⟨cache,topAddress,hcache,htopFrame⟩
  step as ⟨tail,restoreTail,htail,htailLen,hrestoreTail⟩
  step with TopCache.root_ethlib_spec cache seed secret hcache as ⟨root,hroot⟩
  step as ⟨copiedRoot,hcopiedRoot⟩
  step with MessageHashBridge.randomizer_ethlib_spec skPrf message seed as ⟨rho,hrho⟩
  have hkey : (restoreTail copiedRoot).val = seed.val ++ root.val := by
    rw [hrestoreTail,hcopiedRoot,hrestoreHead,hcopiedSeed]
    simp [List.setSlice!,Aeneas.Std.Array.repeat_val,Aeneas.Std.Array.to_slice,List.take_of_length_le]
  step with MessageHashBridge.message_digest_ethlib_spec (restoreTail copiedRoot) message rho seed root hkey as ⟨digest,hdigest⟩
  step as ⟨d30,hd30⟩
  step as ⟨d31,hd31⟩
  step as ⟨d32,hd32⟩
  have h30 : d30 = digest.val[30]! := by rw [getElem!_pos _ 30 (by scalar_tac)]; exact hd30
  have h31 : d31 = digest.val[31]! := by rw [getElem!_pos _ 31 (by scalar_tac)]; exact hd31
  have h32 : d32 = digest.val[32]! := by rw [getElem!_pos _ 32 (by scalar_tac)]; exact hd32
  rw [h30,h31,h32]
  simp only [lift,bind_ok]
  step as ⟨power,hpower⟩
  have hpowerVal : power.val = 262144 := by
    norm_num [Nat.shiftLeft_eq,U32.size,U32.numBits,UScalarTy.numBits] at hpower
    exact hpower
  step as ⟨mask,hmask⟩
  have hmaskEq : mask = 262143#u32 := by apply UScalar.eq_of_val_eq; scalar_tac
  rw [hmaskEq]
  have htree := MessageHashBridge.masked_tree_val digest
  have htreeBound := MessageHashBridge.raw_tree_bound digest
  step as ⟨shifted,hshifted⟩
  have hshiftVal : shifted.val = MessageHashBridge.rawTree digest*256 := by
    rw [htree] at hshifted
    norm_num [Nat.shiftLeft_eq,U32.size,U32.numBits,UScalarTy.numBits] at hshifted
    omega
  step as ⟨d33,hd33⟩
  have h33 : d33 = digest.val[33]! := by rw [getElem!_pos _ 33 (by scalar_tac)]; exact hd33
  rw [h33]
  generalize hidxDef : EthLib.Cryptography.Sphincs.digestIndex (ForsDigest.nativeDigest digest) = idx
  generalize hsourceDef : core.convert.num.FromU64U32.from
    (shifted ||| core.convert.num.FromU32U8.from digest.val[33]!) = sourceIndex
  have hsourceIndex : sourceIndex.val = idx := by
    rw [←hsourceDef,←hidxDef]
    rw [core.convert.num.FromU64U32.from_val_eq,UScalar.val_or,core.convert.num.FromU32U8.from_val_eq,hshiftVal]
    rw [Nat.mul_comm (MessageHashBridge.rawTree digest) 256]
    rw [←Nat.two_pow_add_eq_or_of_lt (show (digest.val[33]!).val < 2^8 by scalar_tac)]
    simpa only [show (2:Nat)^8 = 256 from rfl,MessageHashBridge.rawLeaf,Nat.mul_comm] using
      (MessageHashBridge.digest_index_native digest).symm
  have hbound : idx < 67108864 := by rw [←hidxDef]; exact MessageHashBridge.digest_index_bound digest
  have hidxParts : idx = MessageHashBridge.rawTree digest*256+MessageHashBridge.rawLeaf digest :=
    hidxDef.symm.trans (MessageHashBridge.digest_index_native digest)
  have hleafBound := MessageHashBridge.raw_leaf_bound digest
  have hkeyLeaf : (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf = MessageHashBridge.rawLeaf digest :=
    bottom_index_leaf idx (MessageHashBridge.rawTree digest) (MessageHashBridge.rawLeaf digest)
      hidxParts hleafBound
  have hkeyTree : (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree = MessageHashBridge.rawTree digest :=
    bottom_index_tree idx (MessageHashBridge.rawTree digest) (MessageHashBridge.rawLeaf digest)
      hidxParts hleafBound
  step as ⟨rhoOutput,restoreRho,hrhoOutput,hrhoOutputLen,hrestoreRho⟩
  have hrhoSame : rhoOutput.length = rho.to_slice.length := by
    rw [hrhoOutputLen]
    symm
    simp [Aeneas.Std.Array.to_slice,Slice.length,Slice.from_val]
  step as ⟨copiedRho,hcopiedRho⟩
  have htreeWord : core.convert.num.FromU64U32.from
      ((core.num.U32.from_be_bytes (Aeneas.Std.Array.make 4#usize
        [0#u8,digest.val[30]!,digest.val[31]!,digest.val[32]!])) &&& 262143#u32) =
      treeWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromU64U32.from_val_eq,htree,hkeyTree]
    change MessageHashBridge.rawTree digest = MessageHashBridge.rawTree digest%18446744073709551616
    omega
  rw [htreeWord]
  have hbottomWord : stepWord EthLib.Cryptography.Sphincs.Layer.bottom.toNat = 0#u32 := rfl
  have hscoped := ContextFrame.set_tree_frame_spec topAddress seed .top .bottom 0
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree htopFrame
  rw [hbottomWord] at hscoped
  step with hscoped as ⟨forsAddress,hforsFrame⟩
  step with fors_size_spec as ⟨forsSize,hforsSize⟩
  rw [hforsSize]
  step as ⟨forsEnd,hforsEnd⟩
  have hEndVal : forsEnd.val = 4240 := by scalar_tac
  step as ⟨forsOutput,restoreFors,hforsOutput,hforsOutputLen,hrestoreFors⟩
  have hForsLen : forsOutput.val.length = 4224 := by
    dsimp only [Slice.length] at hforsOutputLen
    omega
  have hleafWord : core.convert.num.FromU32U8.from digest.val[33]! =
      stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromU32U8.from_val_eq,hkeyLeaf]
    have hv := RustCrypto.ClimbBridge.step_word_value (MessageHashBridge.rawLeaf digest) (by omega)
    exact hv.symm
  rw [hleafWord]
  step with ForsSigning.sign_ethlib_spec forsAddress seed secret digest idx forsOutput (by omega) hforsFrame
    as ⟨forsRoot,layerAddress,signedFors,hforsRoot,hlayerFrame,hforsBytes⟩
  step as ⟨loopOffset,hloopOffset⟩
  have ho : loopOffset = 4240#usize := by apply UScalar.eq_of_val_eq; scalar_tac
  rw [ho]
  have hRhoPrefix : (nativeBytes (restoreRho copiedRho).val).take 16 = (nativeNode rho).toList := by
    rw [hrestoreRho,hcopiedRho,native_bytes_set]
    have hl : (nativeBytes rho.to_slice.val).length = 16 := by
      rw [native_bytes_length]
      simp [Aeneas.Std.Array.to_slice,Slice.from_val]
    have h := overwrite_prefix (nativeBytes (Aeneas.Std.Array.repeat 7740#usize 0#u8).val) (nativeBytes rho.to_slice.val) 0 (by
      rw [hl,native_bytes_length]
      scalar_tac)
    simp only [Nat.zero_add,hl,List.take_zero,List.nil_append] at h
    rw [h]
    simpa only [nativeBytes,Aeneas.Std.Array.to_slice,Slice.from_val] using (native_node_list rho).symm
  have hprefix : (nativeBytes (restoreFors signedFors).val).take 4240 = initialBytes seed secret idx digest rho := by
    have hd : (nativeBytes forsOutput.val).drop 4224 = [] := List.drop_eq_nil_iff.mpr (by
      rw [native_bytes_length,hForsLen])
    have hf : nativeBytes signedFors.val =
        (EthLib.Cryptography.Sphincs.encodeFors (ForsSigning.canonicalSign seed secret idx digest).1).data.toList := by
      have hb : nativeBytes signedFors.val =
          (EthLib.Cryptography.Sphincs.encodeFors (ForsSigning.canonicalSign seed secret idx digest).1).data.toList ++
            (nativeBytes forsOutput.val).drop 4224 := by
        simpa only [ForsSigning.asBytes,nativeBytes] using hforsBytes
      simpa only [hd,List.append_nil] using hb
    rw [hrestoreFors,native_bytes_set,hf]
    have hfl : (EthLib.Cryptography.Sphincs.encodeFors (ForsSigning.canonicalSign seed secret idx digest).1).data.toList.length = 4224 := by
      simp [EthLib.Cryptography.Sphincs.encodeFors,EthLib.Base.packBytes,EthLib.Cryptography.Sphincs.Constants.FORS_TREES,
        EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT,EthLib.Cryptography.Sphincs.Constants.TREE_OPENING_SIZE,
        EthLib.Cryptography.Sphincs.Constants.N]
    have hp := overwrite_prefix (nativeBytes (restoreRho copiedRho).val)
      (EthLib.Cryptography.Sphincs.encodeFors (ForsSigning.canonicalSign seed secret idx digest).1).data.toList 16 (by
        rw [hfl,native_bytes_length]
        have hb := (restoreRho copiedRho).property
        scalar_tac)
    unfold initialBytes
    simpa only [hfl,hRhoPrefix] using hp
  step with loop_spec secret limit cache layerAddress sourceIndex (restoreFors signedFors) forsRoot seed idx .bottom
    (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree hsourceIndex hbound hlayerFrame hcache
    as ⟨result,hresult⟩
  unfold publicRefinement
  refine ⟨seed,rho,digest,hseed,?_,?_,?_⟩
  · simpa only [hskPrf,hseed] using hrho
  · have hr : nativeNode root = (KeyGen.publicKey (nativeSeed secret)).root := by
      unfold KeyGen.publicKey
      rw [←hseed]
      exact hroot
    simpa only [hr] using hdigest
  · rw [hprefix,hforsRoot] at hresult
    unfold signFromDigest
    rw [hidxDef]
    exact hresult

end RustCrypto.FullSign
