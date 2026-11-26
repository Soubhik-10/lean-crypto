module
public import RustCrypto.ForsScalarLayout
public import RustCrypto.WotsEthlib
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsRecover
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

abbrev Digits := Aeneas.Std.Array U8 64#usize

def digitRelation (digits : Digits) (word : EthLib.Cryptography.Sphincs.Codeword) : Prop :=
  ∀ chain : Fin EthLib.Cryptography.Sphincs.Constants.V, (digits[chain.val]!).val = (word[chain]).val

@[irreducible] def endValue (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (word : EthLib.Cryptography.Sphincs.Codeword) (chain : Fin EthLib.Cryptography.Sphincs.Constants.V)
    (value : EthLib.Cryptography.Sphincs.Digest) : EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.chain EthLib.Cryptography.Sphincs.hashId (nativeNode seed) key chain
    (word[chain]).val (3-(word[chain]).val) (by
      have hd : (word[chain]).val < 4 := (word[chain]).isLt
      change (word[chain]).val+(3-(word[chain]).val) < 4
      omega) value

def endVector (bytes : List U8) (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) : Vector EthLib.Cryptography.Sphincs.Digest EthLib.Cryptography.Sphincs.Constants.V :=
  Vector.ofFn (fun chain => endValue seed key word chain (nativeNode (ForsRead.nodeAt bytes (16*chain.val))))

def endsBefore (bytes : List U8) (word : EthLib.Cryptography.Sphincs.Codeword) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (count : Nat) : List UInt8 :=
  OrderedPrefix.collect (endVector bytes word seed key) Vector.toList count

theorem chain_frame_head (address : Address) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hframe : keyFrame address seed key .wotsHash) :
    ∃ old2 old3 : Nat, address.val.take 48 = keyHead seed key old2 old3 := by
  rcases hframe with ⟨old2,old3,hhead⟩
  refine ⟨old2.val,old3.val,?_⟩
  have htag : addressTag .wotsHash = 0#u32 := rfl
  simpa only [keyHead,RustCrypto.TreePrimitives.rebuild_word,htag] using hhead

theorem head_chain_frame (address : Address) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hhead : ∃ old2 old3 : Nat, address.val.take 48 = keyHead seed key old2 old3) :
    keyFrame address seed key .wotsHash := by
  rcases hhead with ⟨old2,old3,hhead⟩
  refine ⟨stepWord old2,stepWord old3,?_⟩
  have htag : addressTag .wotsHash = 0#u32 := rfl
  simpa only [keyHead,htag] using hhead

@[step] theorem walk_end_spec (address : Address) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (word : EthLib.Cryptography.Sphincs.Codeword) (chain : Fin EthLib.Cryptography.Sphincs.Constants.V)
    (start : U8) (value : Node) (hstart : start.val = (word[chain]).val)
    (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.walk_chain address (stepWord chain.val) start 3#u8 value ⦃ out =>
      nativeNode out.1 = endValue seed key word chain (nativeNode value) ∧ keyFrame out.2 seed key .wotsHash ⦄ := by
  rcases chain_frame_head address seed key hframe with ⟨old2,old3,hhead⟩
  have hd : (word[chain]).val < 4 := (word[chain]).isLt
  have h3 : (3#u8).val = 3 := rfl
  apply WP.spec_mono (walk_chain_ethlib_spec address seed key chain start 3#u8 value old2 old3 hhead
    (by rw [h3,hstart]; omega) (by decide))
  rintro ⟨root,next⟩ ⟨hroot,hnext⟩
  constructor
  · simpa only [endValue,h3,hstart] using hroot
  · exact head_chain_frame next seed key hnext

end RustCrypto.WotsRecover
