module
public import RustCrypto.ForsPrimitives
public import RustCrypto.Climb
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ClimbBridge
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives
open RustCrypto.WotsEthlib RustCrypto.Climb
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem half_position_val (position : U32) : (halfPosition position).val = position.val / 2 := by
  change (position.bv >>> 1).toNat = position.bv.toNat / 2
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem right_position (position : U32) :
    ((position &&& 1#u32) != 0#u32) = decide (position.val % 2 ≠ 0) := by
  have hzero : (0#u32).val = 0 := rfl
  have hone : (1#u32).val = 1 := rfl
  have hz : position &&& 1#u32 = 0#u32 ↔ position.val % 2 = 0 := by
    constructor
    · intro h
      have hv := congrArg UScalar.val h
      simpa only [UScalar.val_and,hone,hzero,Nat.and_one_is_mod] using hv
    · intro h
      apply UScalar.eq_of_val_eq
      simpa only [UScalar.val_and,hone,hzero,Nat.and_one_is_mod] using h
  by_cases h : position.val % 2 = 0
  · have he := hz.mpr h
    simp only [he,bne_self_eq_false,h,ne_eq,not_true_eq_false,decide_false]
  · have he : position &&& 1#u32 ≠ 0#u32 := fun he => h (hz.mp he)
    simp only [bne_iff_ne,he,h,ne_eq,not_false_eq_true,decide_true]

theorem parent_step_native (address : Address) (node sibling : Node) (position : U32)
    (seed : EthLib.Cryptography.Sphincs.PkSeed) (adrs : EthLib.Cryptography.Sphincs.Adrs)
    (hprefix : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = seed.toList ++ adrs.toList) :
    nativeNode (parentStep address position node sibling).1 =
      EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId seed adrs
        (parentPayload node sibling ((position &&& 1#u32) != 0#u32)) ∧
    (parentStep address position node sibling).2.val.take 48 = address.val.take 48 := by
  constructor
  · apply Vector.toList_inj.1
    simp only [parentStep,parentBytes,native_node_list,Aeneas.Std.Array.from_val]
    rw [parent_input_layout,List.map_take,ByteBridge.digest_native,th_pure_list,
      parent_preimage address node sibling ((position &&& 1#u32) != 0#u32) seed adrs hprefix]
  · simp only [parentStep,parentBytes,Aeneas.Std.Array.from_val,parent_input_layout]
    simp

def addressTag (kind : EthLib.Cryptography.Sphincs.AdrsType) : U32 := stepWord kind.code.toNat

theorem native_tag (kind : EthLib.Cryptography.Sphincs.AdrsType) :
    UInt32.ofBitVec (addressTag kind).bv = kind.code := by
  cases kind <;> rfl

def keyFrame (address : Address) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (kind : EthLib.Cryptography.Sphincs.AdrsType) : Prop :=
  ∃ word2 word3 : U32, address.val.take 48 = headBytes seed (stepWord key.layer.toNat)
    (treeWord key.tree) (addressTag kind) (stepWord key.leaf) word2 word3

@[irreducible] def keyNodeHash (seed : EthLib.Cryptography.Sphincs.PkSeed) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (kind : EthLib.Cryptography.Sphincs.AdrsType) (p : EthLib.Cryptography.Merkle.Position)
    (left right : EthLib.Cryptography.Sphincs.Digest) : Id EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.th EthLib.Cryptography.Sphincs.hashId seed
    (EthLib.Cryptography.Sphincs.keyAdrs kind key p.level p.index)
    (EthLib.Base.packBytes left ++ EthLib.Base.packBytes right)

theorem step_word_value (n : Nat) (h : n < 4294967296) : (stepWord n).val = n := by
  change n % 4294967296 = n
  exact Nat.mod_eq_of_lt h

theorem parent_step_key (address : Address) (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (kind : EthLib.Cryptography.Sphincs.AdrsType) (level : Nat) (position : U32) (node sibling : Node)
    (hlevel : level+1 < 4294967296) (hframe : keyFrame address seed key kind) :
    let nextAddress := positioned address (stepWord (level+1)) (halfPosition position)
    let next := parentStep nextAddress position node sibling
    nativeNode next.1 = keyNodeHash (nativeNode seed) key kind
      ⟨level+1,position.val/2⟩
      (EthLib.Cryptography.Merkle.ordered ⟨level,position.val⟩ (nativeNode node) (nativeNode sibling)).1
      (EthLib.Cryptography.Merkle.ordered ⟨level,position.val⟩ (nativeNode node) (nativeNode sibling)).2 ∧
    keyFrame next.2 seed key kind := by
  dsimp only
  rcases hframe with ⟨old2,old3,hhead⟩
  have hp := positioned_frame address seed (stepWord key.layer.toNat) (treeWord key.tree)
    (addressTag kind) (stepWord key.leaf) old2 old3 (stepWord (level+1)) (halfPosition position) hhead
  have hn : ((positioned address (stepWord (level+1)) (halfPosition position)).val.take 48).map
      (fun b => UInt8.ofBitVec b.bv) = (nativeNode seed).toList ++
      (EthLib.Cryptography.Sphincs.keyAdrs kind key (level+1) (position.val/2)).toList := by
    rw [hp]
    simpa only [step_word_value (level+1) hlevel,half_position_val] using
      RustCrypto.ForsPrimitives.typed_position_head seed key (addressTag kind) kind
        (stepWord (level+1)) (halfPosition position) (native_tag kind)
  have hs := parent_step_native (positioned address (stepWord (level+1)) (halfPosition position))
    node sibling position (nativeNode seed)
    (EthLib.Cryptography.Sphincs.keyAdrs kind key (level+1) (position.val/2)) hn
  constructor
  · rw [hs.1]
    simp only [parentPayload,right_position,keyNodeHash,EthLib.Cryptography.Merkle.ordered,
      EthLib.Cryptography.Merkle.Position.isLeft]
    by_cases he : position.val % 2 = 0 <;> simp [he]
  · exact ⟨stepWord (level+1),halfPosition position,hs.2.trans hp⟩

def nodesBytes (nodes : List Node) : List U8 := nodes.flatMap (fun node => node.val)

/-- The complete source recurrence consumes the exact serialized path and computes the canonical climb. -/
theorem recover_key_complete (nodes : List Node) (tail : List U8) (address : Address) (reader : Slice U8)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (kind : EthLib.Cryptography.Sphincs.AdrsType)
    (level : Nat) (position : U32) (node : Node) (hbound : level+nodes.length < 4294967296)
    (hframe : keyFrame address seed key kind) (hreader : reader.val = nodesBytes nodes ++ tail) :
    ∃ root next remaining,
      recover nodes.length level address reader position node = (some root,next,remaining) ∧
      remaining.val = tail ∧
      nativeNode root = EthLib.Cryptography.Merkle.climb (keyNodeHash (nativeNode seed) key kind)
        ⟨level,position.val⟩ (nativeNode node) (nodes.map nativeNode) ∧
      keyFrame next seed key kind := by
  induction nodes generalizing address reader level position node with
  | nil =>
    refine ⟨node,address,reader,rfl,?_,?_,hframe⟩
    · simpa only [nodesBytes,List.flatMap_nil,List.nil_append] using hreader
    · rfl
  | cons sibling rest ih =>
    have hread : 16 ≤ reader.val.length := by
      rw [hreader]
      simp only [nodesBytes,List.flatMap_cons,List.length_append,List.length_flatMap]
      have hl : sibling.val.length = 16 := by simp
      omega
    have hsize : (16#usize).val = 16 := by scalar_tac
    have hprefix : RustParser.readPrefix 16#usize reader hread = sibling := by
      apply Aeneas.Std.Array.ext
      simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,hreader,nodesBytes,List.flatMap_cons,hsize,List.append_assoc]
      have hl : sibling.val.length = 16 := by simp
      have ht : sibling.val.take 16 = sibling.val := List.take_of_length_le (by omega)
      simp only [List.take_append,ht,hl,Nat.sub_self,Nat.zero_sub,List.take_zero,List.append_nil]
    have hsuffix : (RustParser.readSuffix 16#usize reader).val = nodesBytes rest ++ tail := by
      simp only [RustParser.readSuffix,Slice.from_val,hreader,nodesBytes,List.flatMap_cons,hsize,List.append_assoc]
      have hl : sibling.val.length = 16 := by simp
      have hd : sibling.val.drop 16 = [] := List.drop_eq_nil_iff.mpr (by omega)
      simp only [List.drop_append,hd,hl,Nat.sub_self,Nat.zero_sub,List.drop_zero,List.nil_append]
    have hstep := parent_step_key address seed key kind level position node sibling (by
      simp only [List.length_cons] at hbound
      omega) hframe
    let stepAddress := positioned address (stepWord (level+1)) (halfPosition position)
    let next := parentStep stepAddress position node sibling
    rcases ih next.2 (RustParser.readSuffix 16#usize reader) (level+1) (halfPosition position) next.1
      (by simp only [List.length_cons] at hbound; omega) hstep.2 hsuffix with
      ⟨root,finalAddress,remaining,hresult,hremaining,hnative,hfinal⟩
    refine ⟨root,finalAddress,remaining,?_,hremaining,?_,hfinal⟩
    · simp only [List.length_cons,recover,dite_eq_left hread,hprefix]
      exact hresult
    · rw [hnative]
      simp only [List.map_cons,EthLib.Cryptography.Merkle.climb,EthLib.Cryptography.Merkle.Position.parent,
        half_position_val,Bind.bind]
      rw [hstep.1]

/-- Actual Rust authentication-path recovery equals EthLib and leaves precisely the unread suffix. -/
@[step] theorem climb_key_ethlib_spec (address : Address) (reader : Slice U8) (position height : U32)
    (node seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (kind : EthLib.Cryptography.Sphincs.AdrsType)
    (nodes : List Node) (tail : List U8) (hlen : nodes.length = height.val)
    (hframe : keyFrame address seed key kind) (hreader : reader.val = nodesBytes nodes ++ tail) :
    lean_sphincs.tree.climb address reader position height node ⦃ out =>
      out.1.map nativeNode = some (EthLib.Cryptography.Merkle.climb (keyNodeHash (nativeNode seed) key kind)
        ⟨0,position.val⟩ (nativeNode node) (nodes.map nativeNode)) ∧
      out.2.2.val = tail ∧ keyFrame out.2.1 seed key kind ⦄ := by
  rcases recover_key_complete nodes tail address reader seed key kind 0 position node
    (by rw [hlen]; scalar_tac) hframe hreader with ⟨root,next,remaining,hresult,hremaining,hnative,hnext⟩
  apply WP.spec_mono (climb_spec address reader position height node)
  intro out hout
  rw [← hlen] at hout
  rw [hout,hresult]
  exact ⟨congrArg some hnative,hremaining,hnext⟩

@[step] theorem climb_xmss_ethlib_spec (address : Address) (reader : Slice U8) (position height : U32)
    (node seed : Node) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (nodes : List Node) (tail : List U8) (hlen : nodes.length = height.val)
    (hframe : keyFrame address seed ⟨layer,tree,0⟩ .tree)
    (hreader : reader.val = nodesBytes nodes ++ tail) :
    lean_sphincs.tree.climb address reader position height node ⦃ out =>
      out.1.map nativeNode = some (EthLib.Cryptography.Merkle.climb
        (EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer tree)
        ⟨0,position.val⟩ (nativeNode node) (nodes.map nativeNode)) ∧
      out.2.2.val = tail ∧ keyFrame out.2.1 seed ⟨layer,tree,0⟩ .tree ⦄ := by
  have hhash : keyNodeHash (nativeNode seed) ⟨layer,tree,0⟩ .tree =
      EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer tree := by
    funext p left right
    unfold keyNodeHash
    rfl
  simpa only [hhash] using
    climb_key_ethlib_spec address reader position height node seed ⟨layer,tree,0⟩ .tree nodes tail hlen hframe hreader

end RustCrypto.ClimbBridge
