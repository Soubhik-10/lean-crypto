module
public import RustCrypto.Hash.TweakableBridge
public import RustCrypto.Wots.ChainOrder
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsEthlib
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem positioned_head (address : Address) (chain step : U32) :
    (positioned address chain step).val.take 48 = address.val.take 40 ++
      (core.num.U32.to_be_bytes chain).val ++ (core.num.U32.to_be_bytes step).val := by
  simp [positioned, List.take_append, List.take_of_length_le]

theorem positioned_frame (address : Address) (seed : Node) (layer : U32) (tree : U64)
    (tag pair old2 old3 chain step : U32)
    (hhead : address.val.take 48 = headBytes seed layer tree tag pair old2 old3) :
    (positioned address chain step).val.take 48 = headBytes seed layer tree tag pair chain step := by
  have h40 := congrArg (List.take 40) hhead
  simp only [List.take_take] at h40
  rw [positioned_head]
  have h40' : address.val.take 40 = (headBytes seed layer tree tag pair old2 old3).take 40 := by
    simpa using h40
  rw [h40']
  simp [headBytes, List.take_append, List.take_of_length_le, List.append_assoc]

def treeWord (tree : Nat) : U64 := ⟨BitVec.ofNat 64 tree⟩

@[simp] theorem native_step_word (n : Nat) : UInt32.ofBitVec (stepWord n).bv = UInt32.ofNat n := by rfl
@[simp] theorem native_tree_word (n : Nat) : UInt64.ofBitVec (treeWord n).bv = UInt64.ofNat n := by rfl

@[simp] theorem native_zero : UInt32.ofBitVec (0#u32).bv = 0 := by rfl

def keyHead (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (word2 word3 : Nat) : List U8 :=
  headBytes seed (stepWord key.layer.toNat) (treeWord key.tree) 0#u32
    (stepWord key.leaf) (stepWord word2) (stepWord word3)

theorem key_head_native (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V)
    (step : Fin (EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH-1)) :
    (keyHead seed key chain.val step.val).map (fun b => UInt8.ofBitVec b.bv) =
      (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsChain key chain step).toList := by
  have h := canonical_prefix seed (stepWord key.layer.toNat) (treeWord key.tree) 0#u32
    (stepWord key.leaf) (stepWord chain.val) (stepWord step.val)
  simpa only [keyHead, native_list, native_node_list, native_step_word, native_tree_word, native_zero,
    EthLib.Cryptography.Sphincs.adrsChain, EthLib.Cryptography.Sphincs.keyAdrs,
    EthLib.Cryptography.Sphincs.adrs, EthLib.Cryptography.Sphincs.AdrsType.code] using h

/-- One actual source chain transition is the canonical EthLib chain step. -/
theorem node_step_ethlib (address : Address) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V)
    (step : Fin (EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH-1))
    (old2 old3 : Nat) (node : Node)
    (hhead : address.val.take 48 = keyHead seed key old2 old3) :
    nativeNode (nodeStep address (stepWord chain.val) step.val node).1 =
      EthLib.Cryptography.Sphincs.chainStep EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) key chain step (nativeNode node) ∧
    (nodeStep address (stepWord chain.val) step.val node).2.val.take 48 =
      keyHead seed key chain.val step.val := by
  have hpositioned : (positioned address (stepWord chain.val) (stepWord step.val)).val.take 48 =
      keyHead seed key chain.val step.val :=
    positioned_frame address seed (stepWord key.layer.toNat) (treeWord key.tree) 0#u32
      (stepWord key.leaf) (stepWord old2) (stepWord old3)
      (stepWord chain.val) (stepWord step.val) hhead
  have hnative : ((positioned address (stepWord chain.val) (stepWord step.val)).val.take 48).map
      (fun b => UInt8.ofBitVec b.bv) =
        (nativeNode seed).toList ++ (EthLib.Cryptography.Sphincs.adrsChain key chain step).toList := by
    rw [hpositioned]
    exact key_head_native seed key chain step
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list]
    simp only [nodeStep, Aeneas.Std.Array.from_val]
    rw [List.map_take, ByteBridge.digest_native, EthLib.Cryptography.Sphincs.chainStep,
      th_pure_list, node_preimage _ node (nativeNode seed) _ hnative]
  · simp only [nodeStep, Aeneas.Std.Array.setSlice!_val]
    simpa [List.setSlice!, List.take_of_length_le] using hpositioned

/-- The source's forward chain walk equals EthLib's canonical chain, retaining its address frame. -/
theorem walk_ethlib (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V) (fuel : Nat) :
    ∀ (start old2 old3 : Nat) (address : Address) (node : Node)
      (_hhead : address.val.take 48 = keyHead seed key old2 old3)
      (hbound : start+fuel < EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH),
    nativeNode (walk fuel start (stepWord chain.val) address node).1 =
      EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) key chain start fuel hbound (nativeNode node) ∧
    ∃ word2 word3, (walk fuel start (stepWord chain.val) address node).2.val.take 48 =
      keyHead seed key word2 word3 := by
  induction fuel with
  | zero =>
    intro start old2 old3 address node hhead hbound
    constructor
    · rfl
    · exact ⟨old2,old3,hhead⟩
  | succ fuel ih =>
    intro start old2 old3 address node hhead hbound
    have hstart : start < EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH-1 := by
      simp only [EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH] at hbound ⊢
      omega
    have hs := node_step_ethlib address seed key chain ⟨start,hstart⟩ old2 old3 node hhead
    have hnext : start+1+fuel < EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH := by omega
    have hrec := ih (start+1) chain.val start
      (nodeStep address (stepWord chain.val) start node).2
      (nodeStep address (stepWord chain.val) start node).1 hs.2 hnext
    constructor
    · change nativeNode (walk fuel (start+1) (stepWord chain.val)
        (nodeStep address (stepWord chain.val) start node).2
        (nodeStep address (stepWord chain.val) start node).1).1 = _
      rw [hrec.1]
      simp only [EthLib.Cryptography.Sphincs.chain]
      rw [ChainOrder.chain_cons, hs.1]
    · exact hrec.2

/-- The actual source chain function refines EthLib for every valid WOTS start and stop. -/
@[step] theorem walk_chain_ethlib_spec (address : Address) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey)
    (chain : Fin EthLib.Cryptography.Sphincs.Constants.V)
    (start stop : U8) (node : Node) (old2 old3 : Nat)
    (hhead : address.val.take 48 = keyHead seed key old2 old3)
    (hstart : start.val ≤ stop.val)
    (hstop : stop.val < EthLib.Cryptography.Sphincs.Constants.CHAIN_LENGTH) :
    lean_sphincs.wots.walk_chain address (stepWord chain.val) start stop node ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) key chain start.val (stop.val-start.val) (by omega) (nativeNode node) ∧
      ∃ word2 word3, out.2.val.take 48 = keyHead seed key word2 word3 ⦄ := by
  apply WP.spec_mono (RustCrypto.WotsChain.walk_chain_spec address (stepWord chain.val) start stop node)
  intro out hout
  rw [hout]
  exact walk_ethlib seed key chain (stop.val-start.val) start.val old2 old3 address node hhead (by omega)

end RustCrypto.WotsEthlib
