module
public import RustCrypto.MessageHashFull
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WholeVerifier
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem byte_ne_spec (x y : U8) : core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ ¬(x = y) ⦄ := by
  simp [WP.spec_ok]

theorem native_node_values (left right : Node) : nativeNode left = nativeNode right ↔ left.val = right.val := by
  constructor
  · intro h
    have hl := congrArg Vector.toList h
    rw [native_node_list,native_node_list] at hl
    exact ByteBridge.native_list_injective left.val right.val hl
  · intro h
    apply Vector.toList_inj.1
    rw [native_node_list,native_node_list,h]

theorem key_root_val (key : Aeneas.Std.Array U8 32#usize) : (MessageHashBridge.keyRoot key).val = key.val.drop 16 := by
  unfold MessageHashBridge.keyRoot
  rw [ForsRead.nodeAt_val key.val 16 (by scalar_tac)]
  exact List.take_of_length_le (by scalar_tac)

/-- The actual final Rust byte comparison is equality of canonical root digests. -/
@[step] theorem compare_root_spec (key : Aeneas.Std.Array U8 32#usize) (root : Node) :
    lean_sphincs.verify.closure.Insts.CoreOpsFunctionFnOnceTupleFixedBytes16Bool.call_once key root ⦃ out =>
      out = decide (nativeNode root = nativeNode (MessageHashBridge.keyRoot key)) ⦄ := by
  unfold lean_sphincs.verify.closure.Insts.CoreOpsFunctionFnOnceTupleFixedBytes16Bool.call_once
  simp only [alloy_primitives.bits.fixed.FixedBytes.as_slice,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreOpsIndexIndex.index,
    lean_sphincs.core.ops.index.IndexArray,Aeneas.Std.core.ops.index.IndexArray]
  step as ⟨tail,htail,hlen⟩
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 root.to_slice tail byte_ne_spec)
  intro result hresult
  have heq : root.to_slice = tail ↔ nativeNode root = nativeNode (MessageHashBridge.keyRoot key) := by
    rw [Slice.eq_iff,native_node_values]
    simp only [Aeneas.Std.Array.to_slice,Slice.from_val,htail,key_root_val]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using hresult.trans heq

/-- The actual optional recovery handler accepts exactly a matching recovered root. -/
@[step] theorem option_compare_spec (key : Aeneas.Std.Array U8 32#usize) (root : Option Node) :
    core.option.Option.is_some_and lean_sphincs.verify.closure.Insts.CoreOpsFunctionFnOnceTupleFixedBytes16Bool root key
      ⦃ out => out = ((root.map nativeNode).map
        (fun value => decide (value = nativeNode (MessageHashBridge.keyRoot key)))).getD false ⦄ := by
  cases root with
  | none => simp only [core.option.Option.is_some_and,Option.map_none,Option.getD_none,WP.spec_ok]
  | some node =>
    unfold core.option.Option.is_some_and
    apply WP.spec_mono (compare_root_spec key node)
    intro result hresult
    simpa only [Option.map_some,Option.getD_some] using hresult

end RustCrypto.WholeVerifier
