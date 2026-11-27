module
public import RustCrypto.Wots.Ethlib
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

@[simp] theorem zero_word_bytes : (core.num.U32.to_be_bytes 0#u32).val = List.replicate 4 0#u8 := by
  simp [core.num.U32.to_be_bytes, BitVec.toBEBytes, BitVec.toLEBytes]
  apply UScalar.eq_of_val_eq
  rfl

theorem domain_head (address : Address) (tag pair : U32) :
    (WotsSource.domain address tag pair).val.take 48 = address.val.take 32 ++
      (core.num.U32.to_be_bytes tag).val ++ (core.num.U32.to_be_bytes pair).val ++
      List.replicate 8 0#u8 := by
  simp [WotsSource.domain, List.setSlice!, List.take_append, List.drop_append,
    List.append_assoc, List.take_of_length_le]

theorem domain_frame (address : Address) (seed : Node) (layer : U32) (tree : U64)
    (oldTag oldPair old2 old3 tag pair : U32)
    (hhead : address.val.take 48 = headBytes seed layer tree oldTag oldPair old2 old3) :
    (WotsSource.domain address tag pair).val.take 48 = headBytes seed layer tree tag pair 0#u32 0#u32 := by
  have h32 := congrArg (List.take 32) hhead
  have h32' : address.val.take 32 = (headBytes seed layer tree oldTag oldPair old2 old3).take 32 := by
    simpa only [List.take_take, show min 32 48 = 32 by decide] using h32
  rw [domain_head, h32']
  simp [headBytes, List.take_append, List.take_of_length_le, List.append_assoc]

def typedKeyHead (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (tag : U32) (word2 word3 : Nat) : List U8 :=
  headBytes seed (stepWord key.layer.toNat) (treeWord key.tree) tag
    (stepWord key.leaf) (stepWord word2) (stepWord word3)

theorem prf_head_native (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) :
    (typedKeyHead seed key 5#u32 chain.val 0).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsPrf key chain).toList := by
  have h := canonical_prefix seed (stepWord key.layer.toNat) (treeWord key.tree) 5#u32
    (stepWord key.leaf) (stepWord chain.val) (stepWord 0)
  have hfive : UInt32.ofBitVec (5#u32).bv = 5 := by rfl
  simpa only [typedKeyHead, native_list, native_node_list, native_step_word, native_tree_word, hfive,
    EthLib.Cryptography.Sphincs.adrsPrf, EthLib.Cryptography.Sphincs.keyAdrs,
    EthLib.Cryptography.Sphincs.adrs, EthLib.Cryptography.Sphincs.AdrsType.code] using h

end RustCrypto.WotsEthlib
