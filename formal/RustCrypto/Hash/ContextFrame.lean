module
public import RustCrypto.Tree.Primitives
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ContextFrame
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem update_prefix {α : Type} (bytes values : List α) (offset size : Nat)
    (hupdate : offset+values.length ≤ size) (hsize : size ≤ bytes.length) :
    (bytes.setSlice! offset values).take size = (bytes.take size).setSlice! offset values := by
  simp (disch := omega) [List.setSlice!,List.take_append,List.take_take,List.drop_take,
    List.take_of_length_le]
  omega

theorem zero_tree_bytes : (core.num.U64.to_be_bytes 0#u64).val = List.replicate 8 0#u8 := by
  simp [core.num.U64.to_be_bytes,BitVec.toBEBytes,BitVec.toLEBytes]
  apply UScalar.eq_of_val_eq
  rfl

@[step] theorem context_frame_spec (publicKey : Aeneas.Std.Array U8 32#usize) (seed : Node)
    (hseed : publicKey.val.take 16 = seed.val) :
    lean_sphincs.hash.HashContext.new publicKey ⦃ out => TreePrimitives.frame out seed .bottom 0 ⦄ := by
  apply WP.spec_mono (RustCrypto.context_new_spec publicKey)
  intro address haddress
  refine ⟨0#u32,0#u32,0#u32,0#u32,?_⟩
  rw [haddress,hseed]
  have hz : stepWord EthLib.Cryptography.Sphincs.Layer.bottom.toNat = 0#u32 := rfl
  have ht : treeWord 0 = 0#u64 := rfl
  simp only [headBytes,hz,ht,zero_word_bytes,zero_tree_bytes]
  simp [List.take_append,List.take_of_length_le,List.append_assoc]

/-- Layer/tree changes retain the seed and the rest of the typed address frame. -/
@[step] theorem set_tree_frame_spec (address : Address) (seed : Node)
    (oldLayer layer : EthLib.Cryptography.Sphincs.Layer) (oldTree tree : Nat)
    (hframe : TreePrimitives.frame address seed oldLayer oldTree) :
    lean_sphincs.hash.HashContext.set_tree address (stepWord layer.toNat) (treeWord tree) ⦃ out =>
      TreePrimitives.frame out seed layer tree ⦄ := by
  rcases hframe with ⟨tag,pair,word2,word3,hhead⟩
  apply WP.spec_mono (RustCrypto.set_tree_spec address (stepWord layer.toNat) (treeWord tree))
  intro next hnext
  refine ⟨tag,pair,word2,word3,?_⟩
  rw [hnext,update_prefix _ _ 24 48 (by simp) (by simp),
    update_prefix _ _ 16 48 (by simp) (by simp),hhead]
  simp [headBytes,List.setSlice!,List.take_append,List.drop_append,List.append_assoc,List.take_of_length_le]

end RustCrypto.ContextFrame
