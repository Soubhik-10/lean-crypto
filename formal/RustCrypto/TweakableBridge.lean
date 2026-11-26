module
public import RustCrypto.AddressBridge
public import EthLib.Cryptography.Sphincs.Ots
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TweakableBridge
open RustCrypto.WotsChain RustCrypto.AddressBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def nativeNode (node : Node) : EthLib.Cryptography.Sphincs.Digest :=
  ⟨(node.val.map (fun b => UInt8.ofBitVec b.bv)).toArray, by simp [EthLib.Cryptography.Sphincs.Constants.N]⟩

@[simp] theorem native_node_list (node : Node) :
    (nativeNode node).toList = node.val.map (fun b => UInt8.ofBitVec b.bv) := by rfl

theorem trunc_list {n : Nat} (values : Vector UInt8 n) (r : Nat) (h : r ≤ n) :
    (EthLib.Cryptography.Sphincs.trunc r values h).toList = values.toList.take r := by
  apply List.ext_getElem
  · simp [EthLib.Cryptography.Sphincs.trunc, h]
  · intro i hi hother
    simp [EthLib.Cryptography.Sphincs.trunc]

@[simp] theorem source_bytes_list (values : List U8) :
    (RustCrypto.bytes values).data.toList = values.map (fun b => UInt8.ofBitVec b.bv) := by
  simp [RustCrypto.bytes, ByteBridge.byte_native_eq]

theorem node_preimage (address : Address) (node : Node)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    RustCrypto.bytes (address.val.take 48 ++ node.val) =
      EthLib.Cryptography.Sphincs.thInput seed adrs (EthLib.Base.packBytes (nativeNode node)) := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.1
  simp_all [EthLib.Cryptography.Sphincs.thInput, EthLib.Base.packBytes,
    source_bytes_list, nativeNode, Vector.toList, List.map_append, List.append_assoc]

theorem th_pure_list (seed : EthLib.Cryptography.Sphincs.PkSeed)
    (adrs : EthLib.Cryptography.Sphincs.Adrs) (payload : ByteArray) :
    (EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId seed adrs payload).toList =
      (EthLib.Cryptography.Hash.Keccak.keccak256
        (EthLib.Cryptography.Sphincs.thInput seed adrs payload)).toList.take 16 := by
  calc
    _ = (EthLib.Cryptography.Sphincs.trunc EthLib.Cryptography.Sphincs.Constants.N
      (EthLib.Cryptography.Sphincs.hash (EthLib.Cryptography.Sphincs.thInput seed adrs payload))).toList := by rfl
    _ = (EthLib.Cryptography.Sphincs.hash
      (EthLib.Cryptography.Sphincs.thInput seed adrs payload)).toList.take
        EthLib.Cryptography.Sphincs.Constants.N := trunc_list _ _ _
    _ = _ := by simp only [EthLib.Cryptography.Sphincs.Constants.N]; rfl

/-- The actual source single-node hash is EthLib's canonical addressed hash. -/
@[step] theorem hash_node_ethlib_spec (address : Address) (node : Node)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    lean_sphincs.hash.HashContext.hash_node address node ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId
        seed adrs (EthLib.Base.packBytes (nativeNode node)) ∧
      out.2.val.take 48 = address.val.take 48 ⦄ := by
  apply WP.spec_mono (RustCrypto.hash_node_spec address node)
  rintro ⟨result,next⟩ ⟨hout,hnext⟩
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list, hout, List.map_take, ByteBridge.digest_native]
    rw [th_pure_list, node_preimage address node seed adrs hprefix]
  · rw [hnext]
    simp [List.setSlice!, List.take_of_length_le]

end RustCrypto.TweakableBridge
