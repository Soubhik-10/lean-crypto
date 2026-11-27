module
public import RustCrypto.Tree.Cache.Model
public import RustCrypto.Fors.Primitives
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem positioned_parent_spec (address : Address) (seed left right : Node) (height index : U32)
    (hhead : address.val.take 48 = headBytes seed (stepWord EthLib.Cryptography.Sphincs.Layer.top.toNat)
      (treeWord 0) 2#u32 0#u32 height index) :
    lean_sphincs.hash.HashContext.hash_parent address left right false ⦃ out =>
      nativeNode out.1 = EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId
        (nativeNode seed) .top 0 ⟨height.val,index.val⟩ (nativeNode left) (nativeNode right) ∧
      TreePrimitives.frame out.2 seed .top 0 ⦄ := by
  have hn : (address.val.take 48).map (fun b => UInt8.ofBitVec b.bv) = (nativeNode seed).toList ++
      (EthLib.Cryptography.Sphincs.adrsNode .top 0 height.val index.val).toList := by
    rw [hhead]
    exact TreePrimitives.xmss_parent_head seed .top 0 height index
  apply WP.spec_mono (hash_parent_ethlib_spec address left right false (nativeNode seed)
    (EthLib.Cryptography.Sphincs.adrsNode .top 0 height.val index.val) hn)
  rintro ⟨root,next⟩ ⟨hroot,hnext⟩
  constructor
  · simpa [EthLib.Cryptography.Sphincs.nodeHash,parentPayload] using hroot
  · exact ⟨2#u32,0#u32,height,index,hnext.trans hhead⟩

@[step] theorem parent_body_spec (address : Address) (nodes : Nodes) (seed : Node)
    (height width index : Usize) (hheight : height.val ≤ 10) (hwidth : width.val ≤ 512)
    (hindex : index.val < width.val) (hframe : TreePrimitives.frame address seed .top 0) :
    lean_sphincs.tree.TopTree.new_loop1_loop0.body width height address nodes index ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextNodes,nextIndex) => nextIndex.val = index.val+1 ∧
          TreePrimitives.frame nextAddress seed .top 0 ∧
          ∃ (root : Node) (slot : Usize), slot.val = width.val+index.val ∧ nextNodes = nodes.set slot root ∧
            nativeNode root = EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId
              (nativeNode seed) .top 0 ⟨height.val,index.val⟩
              (nativeNode (nodes[2*(width.val+index.val)]!)) (nativeNode (nodes[2*(width.val+index.val)+1]!)) ⦄ := by
  unfold lean_sphincs.tree.TopTree.new_loop1_loop0.body
  have hrun : index < width := by scalar_tac
  simp only [ite_eq_left hrun,lean_sphincs.tree.HYPERTREE]
  step as ⟨slot,hslot⟩
  step with ForsPrimitives.domain_frame_spec address seed .top 0 2#u32 0#u32 hframe as ⟨scopedAddress,hscoped⟩
  step as ⟨height32,hheight32⟩
  step as ⟨index32,hindex32⟩
  have hh : height32.val = height.val := by scalar_tac
  have hi : index32.val = index.val := by scalar_tac
  step with ForsPrimitives.position_frame_spec scopedAddress seed .top 0 2#u32 0#u32 0#u32 0#u32
    height32 index32 hscoped as ⟨currentAddress,hcurrent⟩
  step as ⟨leftIndex,hleftIndex⟩
  have hlv : leftIndex.val = 2*(width.val+index.val) := by scalar_tac
  step as ⟨left,hleft⟩
  have hl : left = nodes[2*(width.val+index.val)]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos nodes.val (2*(width.val+index.val)) (by scalar_tac)]
    simpa only [hlv] using hleft
  step as ⟨rightIndex,hrightIndex⟩
  have hrv : rightIndex.val = 2*(width.val+index.val)+1 := by scalar_tac
  step as ⟨right,hright⟩
  have hr : right = nodes[2*(width.val+index.val)+1]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos nodes.val (2*(width.val+index.val)+1) (by scalar_tac)]
    simpa only [hrv] using hright
  step with positioned_parent_spec currentAddress seed left right height32 index32 hcurrent
    as ⟨root,nextAddress,hroot,hnextFrame⟩
  step as ⟨nextNodes,hnextNodes⟩
  step as ⟨nextIndex,hnextIndex⟩
  refine ⟨hnextIndex,hnextFrame,root,slot,hslot,hnextNodes,?_⟩
  simpa only [hh,hi,hl,hr] using hroot

end RustCrypto.TopCache
