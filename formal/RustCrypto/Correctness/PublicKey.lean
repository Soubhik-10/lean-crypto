module
public import EthLib.Cryptography.Sphincs.Serialization
public import Init.Data.ByteArray.Lemmas
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
open EthLib.Base EthLib.Cryptography.Sphincs
set_option maxHeartbeats 200000

theorem pack_bytes_size {n : Nat} (bytes : Vector UInt8 n) : (packBytes bytes).size = n := by
  change bytes.toArray.size = n
  exact bytes.size_toArray

theorem public_key_encode_size (key : PublicKey) : (encodePublicKey key).size = 32 := by
  unfold encodePublicKey
  rw [ByteArray.size_append]
  rw [pack_bytes_size key.pkSeed,pack_bytes_size key.root]
  rfl

theorem public_key_decode_encode (key : PublicKey) :
    decodePublicKey (encodePublicKey key) = .ok key := by
  have hs : (encodePublicKey key).size = Constants.PUB_KEY_SIZE := public_key_encode_size key
  unfold decodePublicKey
  rw [dite_eq_left hs]
  have hseed : readBytes (encodePublicKey key) 0 Constants.N (by rw [hs]; decide) = key.pkSeed := by
    apply Vector.ext
    intro i hi
    simp only [readBytes,Vector.getElem_ofFn,Nat.zero_add,encodePublicKey]
    rw [ByteArray.getElem_append_left (by simpa only [pack_bytes_size] using hi)]
    rfl
  have hroot : readBytes (encodePublicKey key) Constants.N Constants.N (by rw [hs]; decide) = key.root := by
    apply Vector.ext
    intro i hi
    simp only [readBytes,Vector.getElem_ofFn,encodePublicKey]
    rw [ByteArray.getElem_append_right (by rw [pack_bytes_size]; exact Nat.le_add_right _ _)]
    simpa only [pack_bytes_size key.pkSeed,Nat.add_sub_cancel_left] using
      (show (packBytes key.root)[i]'(by simpa only [pack_bytes_size key.root] using hi) = key.root[i] from rfl)
  rw [hseed,hroot]

end RustCrypto.CanonicalCorrectness
