module
public import RustCrypto.SigningBytes
public import RustCrypto.WotsPrf
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.KeyMaterial
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def keyInput (seed : EthLib.Cryptography.Sphincs.Seed) (suffix : UInt8) : ByteArray :=
  "leanSPHINCS".toUTF8 ++ EthLib.Base.packBytes seed ++ ⟨#[suffix]⟩

@[irreducible] def publicSeed (seed : EthLib.Cryptography.Sphincs.Seed) : EthLib.Cryptography.Sphincs.PkSeed :=
  EthLib.Cryptography.Sphincs.trunc EthLib.Cryptography.Sphincs.Constants.N (EthLib.Cryptography.Sphincs.hash (keyInput seed 0))

@[irreducible] def secretPrf (seed : EthLib.Cryptography.Sphincs.Seed) : EthLib.Cryptography.Sphincs.HashOutput :=
  EthLib.Cryptography.Sphincs.hash (keyInput seed 1)

theorem key_input_source (seed : Aeneas.Std.Array U8 32#usize) (suffix : U8) :
    RustCrypto.bytes (SigningBytes.seedTag ++ seed.val ++ [suffix]) = keyInput (nativeSeed seed) (UInt8.ofBitVec suffix.bv) := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  rw [source_bytes_list]
  change (SigningBytes.seedTag ++ seed.val ++ [suffix]).map (fun b => UInt8.ofBitVec b.bv) =
    [108,101,97,110,83,80,72,73,78,67,83] ++ (nativeSeed seed).toList ++ [UInt8.ofBitVec suffix.bv]
  simp only [List.map_append,List.map_cons,List.map_nil,native_seed_list,SigningBytes.seedTag]
  rfl

/-- Both key-expansion outputs refine the domain-separated native Keccak definitions. -/
@[step] theorem expand_key_ethlib_spec (seed : Aeneas.Std.Array U8 32#usize) :
    lean_sphincs.signing.expand_key seed ⦃ out =>
      nativeNode out.1 = publicSeed (nativeSeed seed) ∧ nativeSeed out.2 = secretPrf (nativeSeed seed) ⦄ := by
  apply WP.spec_mono (SigningBytes.expand_key_spec seed)
  rintro ⟨pkSeed,skPrf⟩ ⟨hpublic,hsecret⟩
  dsimp only at hpublic hsecret ⊢
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list,hpublic,List.map_take,ByteBridge.digest_native]
    unfold publicSeed
    rw [trunc_list]
    simp only [EthLib.Cryptography.Sphincs.Constants.N]
    unfold EthLib.Cryptography.Sphincs.hash
    rw [key_input_source]
    rfl
  · apply Vector.toList_inj.1
    rw [native_seed_list,hsecret,ByteBridge.digest_native]
    unfold secretPrf EthLib.Cryptography.Sphincs.hash
    rw [key_input_source]
    rfl

end RustCrypto.KeyMaterial
