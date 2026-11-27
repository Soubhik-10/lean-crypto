module
public import RustCrypto.Verification.Message.Bridge
public import RustCrypto.Fors.Scalar.Layout
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.MessageHashBridge
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem message_input (publicKey message : Aeneas.Std.Array U8 32#usize) (rho seed root : Node)
    (counter : List U8) (hkey : publicKey.val = seed.val ++ root.val) :
    RustCrypto.bytes (rho.val ++ publicKey.val ++ message.val ++ counter) =
      EthLib.Base.packBytes (nativeNode rho) ++ EthLib.Base.packBytes (nativeNode seed) ++
        EthLib.Base.packBytes (nativeNode root) ++ EthLib.Base.packBytes (nativeSeed message) ++ RustCrypto.bytes counter := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  simp [source_bytes_list,EthLib.Base.packBytes,nativeSeed,nativeNode,hkey,List.map_append,List.append_assoc]

/-- The actual 34-byte source digest is exactly EthLib's ordered H_msg expansion. -/
@[step] theorem message_digest_ethlib_spec (publicKey message : Aeneas.Std.Array U8 32#usize) (rho seed root : Node)
    (hkey : publicKey.val = seed.val ++ root.val) :
    lean_sphincs.hash.message_digest publicKey message rho ⦃ out => ForsDigest.nativeDigest out =
      EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.hashId (nativeNode rho) (nativeNode seed)
        (nativeNode root) (nativeSeed message) ⦄ := by
  apply WP.spec_mono (RustCrypto.message_digest_spec publicKey message rho)
  intro out hout
  apply Vector.toList_inj.1
  rw [native_digest_list,hout,List.map_append,List.map_take,ByteBridge.digest_native,ByteBridge.digest_native]
  rw [message_input publicKey message rho seed root [0#u8,0#u8,0#u8,0#u8] hkey,
      message_input publicKey message rho seed root [0#u8,0#u8,0#u8,1#u8] hkey]
  exact (hmsg_list EthLib.Cryptography.Sphincs.hashId (nativeNode rho) (nativeNode seed)
    (nativeNode root) (nativeSeed message)).symm

def keySeed (publicKey : Aeneas.Std.Array U8 32#usize) : Node := ForsRead.nodeAt publicKey.val 0

def keyRoot (publicKey : Aeneas.Std.Array U8 32#usize) : Node := ForsRead.nodeAt publicKey.val 16

theorem public_key_parts (publicKey : Aeneas.Std.Array U8 32#usize) :
    publicKey.val = (keySeed publicKey).val ++ (keyRoot publicKey).val := by
  have hl : publicKey.val.length = 32 := publicKey.property
  unfold keySeed keyRoot
  rw [ForsRead.nodeAt_val publicKey.val 0 (by omega),ForsRead.nodeAt_val publicKey.val 16 (by omega)]
  simp only [List.drop_zero]
  rw [List.take_of_length_le (show (publicKey.val.drop 16).length ≤ 16 by simp only [List.length_drop]; omega)]
  exact (List.take_append_drop 16 publicKey.val).symm

/-- Canonical digest refinement for every public-key byte string, with its exact seed/root split. -/
@[step] theorem message_digest_bytes_ethlib_spec (publicKey message : Aeneas.Std.Array U8 32#usize) (rho : Node) :
    lean_sphincs.hash.message_digest publicKey message rho ⦃ out => ForsDigest.nativeDigest out =
      EthLib.Cryptography.Sphincs.hMsg EthLib.Cryptography.Sphincs.hashId (nativeNode rho) (nativeNode (keySeed publicKey))
        (nativeNode (keyRoot publicKey)) (nativeSeed message) ⦄ := by
  exact message_digest_ethlib_spec publicKey message rho (keySeed publicKey) (keyRoot publicKey) (public_key_parts publicKey)

end RustCrypto.MessageHashBridge
