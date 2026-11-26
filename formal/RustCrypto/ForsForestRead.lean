module
public import RustCrypto.ForsForestClosures
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsForest
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

@[step] theorem take_batch_spec (reader : Slice U8) (hreader : 352 ≤ reader.val.length) :
    lean_sphincs.signature.Reader.take 352#usize reader ⦃ out =>
      out = (some (RustParser.readPrefix 352#usize reader hreader),RustParser.readSuffix 352#usize reader) ⦄ := by
  rw [RustParser.take_success 352#usize reader hreader]
  simp only [WP.spec_ok]

@[step] theorem first_batch_spec (block : Aeneas.Std.Array U8 352#usize) :
    core.slice.Slice.first_chunk 2#usize (RustCrypto.chunks 176#usize (Aeneas.Std.Array.to_slice block))
      ⦃ out => ∃ batch : Aeneas.Std.Array (Aeneas.Std.Array U8 176#usize) 2#usize,
        out = some batch ∧ ∀ j < width, (batch[j]!).val = (block.val.drop (176*j)).take 176 ⦄ := by
  have hlen : (RustCrypto.chunks 176#usize (Aeneas.Std.Array.to_slice block)).val.length = width := by
    simp [RustCrypto.chunks,Aeneas.Std.Array.to_slice,width]
  have hbound : (2#usize).val ≤ (RustCrypto.chunks 176#usize (Aeneas.Std.Array.to_slice block)).val.length := by
    change width ≤ _
    omega
  simp only [core.slice.Slice.first_chunk,dite_eq_left hbound,WP.spec_ok]
  refine ⟨_,rfl,?_⟩
  intro j hj
  rw [Aeneas.Std.Array.getElem!_Nat_eq,getElem!_pos _ j (by scalar_tac)]
  simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,List.getElem_take,
    RustCrypto.chunks,Slice.from_val,List.getElem_ofFn,RustCrypto.chunk,Aeneas.Std.Array.to_slice]
  change ((block.val.drop (j*176)).take 176) = (block.val.drop (176*j)).take 176
  rw [Nat.mul_comm j 176]

end RustCrypto.ForsForest
