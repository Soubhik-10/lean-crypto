module
public import RustCrypto.Keygen.Material
public import RustCrypto.Fors.DigestBridge
public import RustCrypto.Common.VectorFlatten
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.MessageHashBridge
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem native_digest_list (digest : Aeneas.Std.Array U8 34#usize) :
    (ForsDigest.nativeDigest digest).toList = digest.val.map (fun b => UInt8.ofBitVec b.bv) := by
  apply List.ext_getElem
  · simp only [Vector.length_toList,List.length_map]
    exact digest.property.symm
  · intro j hj hother
    simp only [Vector.getElem_toList,ForsDigest.nativeDigest,Vector.getElem_ofFn,List.getElem_map,ByteBridge.byte_native_eq]

/-- Native framing of the deterministic signing randomizer. -/
theorem randomizer_input (skPrf message : Aeneas.Std.Array U8 32#usize) (pkSeed : Node) :
    RustCrypto.bytes (skPrf.val ++ pkSeed.val ++ [0#u8,11#u8] ++ SigningBytes.seedTag ++ message.val) =
      EthLib.Base.packBytes (nativeSeed skPrf) ++ EthLib.Base.packBytes (nativeNode pkSeed) ++
        EthLib.Cryptography.Sphincs.framedMessage (nativeSeed message) := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  simp [EthLib.Cryptography.Sphincs.framedMessage,EthLib.Cryptography.Sphincs.Constants.SEED_TAG,
    EthLib.Base.packBytes,source_bytes_list,nativeSeed,nativeNode,SigningBytes.seedTag,
    List.map_append,List.append_assoc]

@[step] theorem randomizer_ethlib_spec (skPrf message : Aeneas.Std.Array U8 32#usize) (pkSeed : Node) :
    lean_sphincs.signing.randomizer skPrf pkSeed message ⦃ out => nativeNode out =
      EthLib.Cryptography.Sphincs.prfMsg EthLib.Cryptography.Sphincs.hashId
        (nativeSeed skPrf) (nativeNode pkSeed) (nativeSeed message) ⦄ := by
  apply WP.spec_mono (SigningBytes.randomizer_spec skPrf message pkSeed)
  intro out hout
  apply Vector.toList_inj.1
  rw [native_node_list,hout,List.map_take,ByteBridge.digest_native]
  change _ = (EthLib.Cryptography.Sphincs.trunc EthLib.Cryptography.Sphincs.Constants.N
    (EthLib.Cryptography.Sphincs.hash (EthLib.Base.packBytes (nativeSeed skPrf) ++ EthLib.Base.packBytes (nativeNode pkSeed) ++
      EthLib.Cryptography.Sphincs.framedMessage (nativeSeed message)))).toList
  rw [trunc_list]
  simp only [EthLib.Cryptography.Sphincs.Constants.N]
  unfold EthLib.Cryptography.Sphincs.hash
  rw [randomizer_input]
  rfl

/-- Ordered flattening of the two H_msg calls. -/
theorem two_flatten_list (f : Fin 2 → Vector UInt8 32) :
    (Vector.ofFn f).flatten.toList = (f 0).toList ++ (f 1).toList := by
  have hf : (Vector.ofFn f).flatten.toList = (Vector.ofFn f).toList.flatMap Vector.toList :=
    OrderedVector.flatten_list (Vector.ofFn f)
  rw [hf,Vector.toList_ofFn]
  simp [List.ofFn_succ]

/-- H_msg is exactly two ordered counter calls, retaining all of the first and two bytes of the second. -/
theorem hmsg_list (H : ByteArray → Id (Vector UInt8 32))
    (rho : EthLib.Cryptography.Sphincs.Randomizer) (pkSeed : EthLib.Cryptography.Sphincs.PkSeed)
    (pkRoot : EthLib.Cryptography.Sphincs.Digest) (message : EthLib.Cryptography.Sphincs.Message) :
    (EthLib.Cryptography.Sphincs.hMsg H rho pkSeed pkRoot message).toList =
      (H (EthLib.Base.packBytes rho ++ EthLib.Base.packBytes pkSeed ++ EthLib.Base.packBytes pkRoot ++
        EthLib.Base.packBytes message ++ ⟨#[0,0,0,0]⟩)).toList ++
      (H (EthLib.Base.packBytes rho ++ EthLib.Base.packBytes pkSeed ++ EthLib.Base.packBytes pkRoot ++
        EthLib.Base.packBytes message ++ ⟨#[0,0,0,1]⟩)).toList.take 2 := by
  unfold EthLib.Cryptography.Sphincs.hMsg
  simp only [OrderedVector.ofFnInOrder_id]
  change (EthLib.Cryptography.Sphincs.trunc 34 ((Vector.ofFn (fun i : Fin 2 =>
    H (EthLib.Base.packBytes rho ++ EthLib.Base.packBytes pkSeed ++ EthLib.Base.packBytes pkRoot ++
      EthLib.Base.packBytes message ++ EthLib.Base.packBytes (EthLib.Cryptography.Sphincs.toByte 4 i.val)))).flatten)).toList = _
  rw [trunc_list,two_flatten_list]
  simp [List.take_append,List.take_of_length_le]
  rfl

end RustCrypto.MessageHashBridge
