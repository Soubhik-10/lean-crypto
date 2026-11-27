module
public import RustCrypto.Wots.Signing.Full
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TweakableBridge
open RustCrypto.WotsChain RustCrypto.AddressBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def parentPayload (value sibling : Node) (right : Bool) : ByteArray :=
  if right then EthLib.Base.packBytes (nativeNode sibling) ++ EthLib.Base.packBytes (nativeNode value)
  else EthLib.Base.packBytes (nativeNode value) ++ EthLib.Base.packBytes (nativeNode sibling)

theorem parent_input_layout (address : Address) (value sibling : Node) (right : Bool) :
    ((address.val.setSlice! 48 (if right then sibling.val else value.val)).setSlice!
      64 (if right then value.val else sibling.val)) =
      address.val.take 48 ++ (if right then sibling.val else value.val) ++
        (if right then value.val else sibling.val) := by
  cases right <;> simp [List.setSlice!,List.take_append,List.append_assoc,List.take_of_length_le]

theorem parent_preimage (address : Address) (value sibling : Node) (right : Bool)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    RustCrypto.bytes (address.val.take 48 ++ (if right then sibling.val else value.val) ++
      (if right then value.val else sibling.val)) =
      EthLib.Cryptography.Sphincs.thInput seed adrs (parentPayload value sibling right) := by
  cases right <;> apply ByteArray.ext <;> apply _root_.Array.toList_inj.1 <;>
    simp_all [parentPayload,EthLib.Cryptography.Sphincs.thInput,EthLib.Base.packBytes,
      source_bytes_list,nativeNode,Vector.toList,List.map_append,List.append_assoc]

/-- Actual source parent hashing equals the canonical addressed hash in either sibling order. -/
@[step] theorem hash_parent_ethlib_spec (address : Address) (value sibling : Node) (right : Bool)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    lean_sphincs.hash.HashContext.hash_parent address value sibling right ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId seed adrs
        (parentPayload value sibling right) ∧ out.2.val.take 48 = address.val.take 48 ⦄ := by
  apply WP.spec_mono (RustCrypto.hash_parent_spec address value sibling right)
  rintro ⟨result,next⟩ ⟨hout,hnext⟩
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list,hout,parent_input_layout,List.map_take,ByteBridge.digest_native,
      th_pure_list,parent_preimage address value sibling right seed adrs hprefix]
  · rw [hnext,parent_input_layout]
    cases right <;> simp

end RustCrypto.TweakableBridge
