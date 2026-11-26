module
public import RustCrypto.WotsAvx2Group
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib RustCrypto.ClimbBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

@[step] theorem single_hash_spec (address : Address) (node : Node) (selected offset : Usize) (step : U8)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hselected : selected.val < 16) (hoffset : offset.val+16 ≤ 64)
    (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.hash.HashContext.hash_node (groupAddress address selected offset step) node ⦃ out =>
      nativeNode out.1 = chainHash seed key (offset.val+selected.val) step.val (nativeNode node) ∧
      keyFrame out.2 seed key .wotsHash ⦄ := by
  apply WP.spec_mono (RustCrypto.hash_node_spec (groupAddress address selected offset step) node)
  rintro ⟨root,nextAddress⟩ ⟨hroot,hnext⟩
  dsimp only at hroot hnext ⊢
  constructor
  · apply Vector.toList_inj.1
    rw [native_node_list,hroot,List.map_take,ByteBridge.digest_native]
    unfold chainHash
    rw [th_pure_list]
    rw [node_preimage _ node (nativeNode seed) _
      (group_prefix_native address selected offset step seed key hselected hoffset hframe)]
  · rcases group_positioned_frame address selected offset step seed key hframe with ⟨w2,w3,hhead⟩
    refine ⟨w2,w3,?_⟩
    calc
      _ = (groupAddress address selected offset step).val.take 48 := by
        rw [hnext]
        simp [List.setSlice!,List.take_of_length_le]
      _ = _ := hhead

@[step] theorem tail_body_spec (address : Address) (nodes : Aeneas.Std.Array Node 16#usize)
    (offset : Usize) (step : U8) (chains : Aeneas.Std.Array Usize 4#usize) (count tail : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (htail : tail.val < count.val) (hcount : count.val ≤ 4) (hoffset : offset.val+16 ≤ 64)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) (hframe : keyFrame address seed key .wotsHash) :
    lean_sphincs.wots.recover_window_loop0_loop1.body offset step chains count address nodes tail ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextNodes,nextTail) => nextTail.val = tail.val+1 ∧
          keyFrame nextAddress seed key .wotsHash ∧
          ∃ root : Node, nextNodes = nodes.set (chains[tail.val]!) root ∧
            nativeNode root = chainHash seed key (offset.val+(chains[tail.val]!).val) step.val
              (nativeNode (nodes[(chains[tail.val]!).val]!)) ⦄ := by
  unfold lean_sphincs.wots.recover_window_loop0_loop1.body
  have hrun : tail < count := by scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨selected,hselected⟩
  have hs : selected = chains[tail.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos chains.val tail.val (by scalar_tac)]
    exact hselected
  have hbound : selected.val < 16 := by rw [hs]; exact hchains tail.val (by omega)
  step as ⟨sum,hsum⟩
  step as ⟨chainWord,hchainWord⟩
  step with widen_step_spec step as ⟨stepWordValue,hstepWord⟩
  step with RustCrypto.set_position_spec address chainWord stepWordValue as ⟨updated,hupdated⟩
  have hchainEq : chainWord = stepWord (offset.val+selected.val) := by
    apply UScalar.eq_of_val_eq
    change chainWord.val = (offset.val+selected.val)%4294967296
    rw [Nat.mod_eq_of_lt (by omega)]
    scalar_tac
  have hstepEq : stepWordValue = stepWord step.val := by
    apply UScalar.eq_of_val_eq
    change stepWordValue.val = step.val%4294967296
    rw [Nat.mod_eq_of_lt (by scalar_tac)]
    exact hstepWord
  have hu : updated = groupAddress address selected offset step := by
    apply Aeneas.Std.Array.ext
    simpa only [groupAddress,positioned,Aeneas.Std.Array.from_val,hchainEq,hstepEq] using hupdated
  rw [hu]
  step as ⟨value,hvalue⟩
  have hv : value = nodes[selected.val]! := by
    rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos nodes.val selected.val (by scalar_tac)]
    exact hvalue
  rw [hv]
  step with single_hash_spec address (nodes[selected.val]!) selected offset step seed key hbound hoffset hframe
    as ⟨root,nextAddress,hroot,hnextFrame⟩
  step as ⟨nextNodes,hnextNodes⟩
  step as ⟨nextTail,hnextTail⟩
  refine ⟨hnextTail,hnextFrame,root,?_,?_⟩
  · simpa only [hs] using hnextNodes
  · simpa only [hs] using hroot

end RustCrypto.WotsAvx2
