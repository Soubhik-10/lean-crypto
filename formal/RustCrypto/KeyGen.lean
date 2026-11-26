module
public import RustCrypto.KeyMaterial
public import RustCrypto.ContextFrame
public import RustCrypto.TreeConstruction
public import RustIndex
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.KeyGen
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[irreducible] def publicKey (secret : EthLib.Cryptography.Sphincs.Seed) : EthLib.Cryptography.Sphincs.PublicKey :=
  let pkSeed := KeyMaterial.publicSeed secret
  ⟨pkSeed,EthLib.Cryptography.Sphincs.treeRoot EthLib.Cryptography.Sphincs.hashId pkSeed
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId pkSeed secret) .top 0⟩

@[step] theorem max_tree_height_spec : lean_sphincs.params.MAX_TREE_HEIGHT ⦃ out => out = 10#usize ⦄ := by
  unfold lean_sphincs.params.MAX_TREE_HEIGHT
  step as ⟨height,hheight⟩
  have hh : height = 10#u32 := by simpa [RustIndex.layer_heights_eq] using hheight
  rw [hh]
  apply UScalar.eq_of_val_eq
  scalar_tac

/-- Public key generation returns the canonical top-tree root after domain-separated seed expansion. -/
@[step] theorem key_gen_ethlib_spec (secret : Aeneas.Std.Array U8 32#usize) :
    lean_sphincs.signing.key_gen secret ⦃ out =>
      RustCrypto.bytes out.val = EthLib.Cryptography.Sphincs.encodePublicKey (publicKey (nativeSeed secret)) ⦄ := by
  unfold lean_sphincs.signing.key_gen
  step with KeyMaterial.expand_key_ethlib_spec secret as ⟨pkSeed,skPrf,hpkSeed,hskPrf⟩
  simp only [alloy_primitives.bits.fixed.FixedBytes.ZERO,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndexMut.index_mut,
    alloy_primitives.bits.fixed.FixedBytes.as_slice,lean_sphincs.params.NODE_BYTES,
    lean_sphincs.core.ops.index.IndexMutArray,Aeneas.Std.core.ops.index.IndexMutArray]
  step as ⟨head,restore,hhead,hlen,hrestore⟩
  step as ⟨copied,hcopied⟩
  have hseed : (restore copied).val.take 16 = pkSeed.val := by
    rw [hrestore,hcopied]
    simp [List.setSlice!,Aeneas.Std.Array.repeat_val,Aeneas.Std.Array.to_slice,List.take_of_length_le]
  step with ContextFrame.context_frame_spec (restore copied) pkSeed hseed as ⟨address,haddress⟩
  have hl : stepWord EthLib.Cryptography.Sphincs.Layer.top.toNat = 2#u32 := rfl
  have ht : treeWord 0 = 0#u64 := rfl
  have htop := ContextFrame.set_tree_frame_spec address pkSeed .bottom .top 0 0 haddress
  simp only [hl,ht] at htop
  step with htop as ⟨topAddress,htopAddress⟩
  step with max_tree_height_spec as ⟨height,hheight⟩
  rw [hheight]
  step as ⟨height32,hheight32⟩
  have hh : height32 = 10#u32 := by apply UScalar.eq_of_val_eq; scalar_tac
  rw [hh]
  step as ⟨path,restorePath,hpath,hrestorePath⟩
  step with RustCrypto.BuildRoot.build_xmss_root_ethlib_spec topAddress pkSeed secret .top 0 10#u32 0#u32 path
    (by rfl) htopAddress as ⟨root,nextAddress,remaining,hroot,hnextFrame⟩
  step as ⟨tail,restoreTail,htail,htailLen,hrestoreTail⟩
  step as ⟨copiedRoot,hcopiedRoot⟩
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  rw [source_bytes_list,hrestoreTail,hcopiedRoot]
  have hraw : ((restore copied).val.setSlice! 16 root.to_slice.val) = pkSeed.val ++ root.val := by
    rw [hrestore,hcopied]
    simp [List.setSlice!,Aeneas.Std.Array.repeat_val,Aeneas.Std.Array.to_slice,List.take_of_length_le]
  rw [hraw,List.map_append,←native_node_list pkSeed,←native_node_list root,hroot,hpkSeed]
  unfold publicKey EthLib.Cryptography.Sphincs.encodePublicKey
  rfl

end RustCrypto.KeyGen
