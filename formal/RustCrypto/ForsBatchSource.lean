module
public import RustCrypto.ForsBatchWalk
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def leafStep (address : Address) (opening : Aeneas.Std.Array U8 176#usize) (position : U32) : Node × Address :=
  let current := positioned address 0#u32 position
  let secret := readNode opening 0
  (Aeneas.Std.Array.from ((RustCrypto.digest (current.val.take 48 ++ secret.val)).val.take 16) (by simp),
    current.setSlice! 48 secret.val)

/-- The entire extracted SIMD FORS batch is lane-wise leaf hashing followed by ten parent steps. -/
@[step] theorem recover_batch_spec (addresses : Aeneas.Std.Array Address 2#usize)
    (openings : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize)
    (positions : Aeneas.Std.Array U32 2#usize) :
    lean_sphincs.fors.recover_batch addresses openings positions ⦃ out =>
      ∀ j < 2, (out.1[j]!,out.2[j]!) =
        walk (openings[j]!) 10 0 (positions[j]!)
          (leafStep (addresses[j]!) (openings[j]!) (positions[j]!)).1
          (leafStep (addresses[j]!) (openings[j]!) (positions[j]!)).2 ⦄ := by
  unfold lean_sphincs.fors.recover_batch
  step with BatchPositions.set_positions_spec addresses 0#u32 positions as ⟨positionedAddresses,hpositioned⟩
  step with first_array_spec openings as ⟨first,hfirst⟩
  step with BatchNodes.hash_nodes_spec positionedAddresses first as ⟨nodes,hashedAddresses,hnodes,haddresses⟩
  apply WP.spec_mono (batch_loop_spec hashedAddresses openings positions nodes 0#u32 (by decide))
  intro out hout j hj
  have hp : positionedAddresses[j]! = positioned (addresses[j]!) 0#u32 (positions[j]!) := by
    apply Aeneas.Std.Array.ext
    simpa only [positioned,Aeneas.Std.Array.from_val,BatchPositions.addressBytes] using hpositioned j hj
  have hf : first[j]! = readNode (openings[j]!) 0 := by
    apply Aeneas.Std.Array.ext
    rw [readNode_eq _ _ (by decide),nodeAt_val]
    exact hfirst j hj
  have hn : nodes[j]! = (leafStep (addresses[j]!) (openings[j]!) (positions[j]!)).1 := by
    apply Aeneas.Std.Array.ext
    simp only [leafStep,Aeneas.Std.Array.from_val]
    rw [hnodes j hj,hp,hf]
  have ha : hashedAddresses[j]! = (leafStep (addresses[j]!) (openings[j]!) (positions[j]!)).2 := by
    apply Aeneas.Std.Array.ext
    simp only [leafStep,Aeneas.Std.Array.setSlice!_val]
    rw [haddresses j hj,hp,hf]
  have hz : (0#u32).val = 0 := rfl
  simpa only [hz,Nat.sub_zero,hn,ha] using hout j hj

end RustCrypto.ForsBatch
