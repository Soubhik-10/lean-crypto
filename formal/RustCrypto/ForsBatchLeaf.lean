module
public import RustCrypto.ForsBatchSource
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.WotsEthlib RustCrypto.AddressBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

theorem leaf_step_native (address : Address) (opening : Aeneas.Std.Array U8 176#usize) (position : U32)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hframe : keyFrame address seed key .forsTree) :
    nativeNode (leafStep address opening position).1 =
      EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.keyAdrs .forsTree key 0 position.val)
        (EthLib.Base.packBytes (nativeNode (readNode opening 0))) ∧
    keyFrame (leafStep address opening position).2 seed key .forsTree := by
  rcases hframe with ⟨old2,old3,hhead⟩
  let current := positioned address 0#u32 position
  have hc : current.val.take 48 = headBytes seed (stepWord key.layer.toNat) (treeWord key.tree)
      (addressTag .forsTree) (stepWord key.leaf) 0#u32 position :=
    positioned_frame address seed (stepWord key.layer.toNat) (treeWord key.tree)
      (addressTag .forsTree) (stepWord key.leaf) old2 old3 0#u32 position hhead
  have hz : (0#u32).val = 0 := rfl
  have hn : (current.val.take 48).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.keyAdrs .forsTree key 0 position.val).toList := by
    rw [hc]
    simpa only [hz] using ForsPrimitives.typed_position_head seed key (addressTag .forsTree)
      .forsTree 0#u32 position (native_tag .forsTree)
  have hb := node_preimage current (readNode opening 0) (nativeNode seed)
    (EthLib.Cryptography.Sphincs.keyAdrs .forsTree key 0 position.val) hn
  constructor
  · apply Vector.toList_inj.1
    simp only [leafStep,native_node_list,Aeneas.Std.Array.from_val]
    rw [List.map_take,ByteBridge.digest_native,th_pure_list]
    exact congrArg (fun bytes => (EthLib.Cryptography.Hash.Keccak.keccak256 bytes).toList.take 16) hb
  · refine ⟨0#u32,position,?_⟩
    calc
      _ = current.val.take 48 := by
        simp [leafStep,current,Aeneas.Std.Array.setSlice!_val,List.setSlice!,List.take_of_length_le]
      _ = _ := hc

end RustCrypto.ForsBatch
