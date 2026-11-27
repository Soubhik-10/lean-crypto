module
public import RustCrypto.Serialization.Writer
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.AppendNodes
abbrev Node := RustCrypto.Writer.Node

@[step] theorem body_success {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (hasher : List U8) (i : Usize) (hi : i.val < N.val) :
    lean_sphincs.hash.append_nodes_loop.body nodes hasher i ⦃ result =>
      match result with
      | .cont (next, j) => j.val = i.val + 1 ∧
          next = hasher ++ (nodes.val[i.val]'(by simpa using hi)).val
      | .done _ => False ⦄ := by
  unfold lean_sphincs.hash.append_nodes_loop.body
  simp only [alloy_primitives.utils.Keccak256.update,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreConvertAsRefSliceU8.as_ref]
  step*

@[step] theorem body_done {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (hasher : List U8) (i : Usize) (hi : N.val ≤ i.val) :
    lean_sphincs.hash.append_nodes_loop.body nodes hasher i ⦃ result =>
      result = .done hasher ⦄ := by
  have hstop : ¬ i < N := by scalar_tac
  simp [lean_sphincs.hash.append_nodes_loop.body, hstop, WP.spec_ok]

@[step] theorem loop_spec {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (initial hasher : List U8) (i : Usize) (hi : i.val ≤ N.val)
    (hbytes : hasher = initial ++ Writer.headBytes nodes i.val) :
    lean_sphincs.hash.append_nodes_loop hasher nodes i ⦃ out =>
      out = initial ++ Writer.headBytes nodes N.val ⦄ := by
  unfold lean_sphincs.hash.append_nodes_loop
  apply loop.spec_decr_nat
    (fun state : List U8 × Usize => N.val - state.2.val)
    (fun state : List U8 × Usize => state.2.val ≤ N.val ∧
      state.1 = initial ++ Writer.headBytes nodes state.2.val)
  · rintro ⟨current, j⟩ ⟨hjn, hcurrent⟩
    dsimp only at hjn hcurrent
    by_cases hrun : j.val < N.val
    · apply WP.spec_mono (body_success nodes current j hrun)
      intro result hr
      cases result with
      | done value => exact False.elim hr
      | cont state =>
        rcases state with ⟨next, nextJ⟩
        rcases hr with ⟨hj, hn⟩
        constructor
        · dsimp only
          rw [hj]
          constructor
          · omega
          · rw [Writer.prefix_succ nodes j.val hrun, hn, hcurrent, List.append_assoc]
        · dsimp only
          rw [hj]
          omega
    · apply WP.spec_mono (body_done nodes current j (by omega))
      intro result hr
      subst result
      have hj : j.val = N.val := by omega
      simpa only [hj] using hcurrent
  · exact ⟨hi, hbytes⟩

/-- Compression receives every node once, in the original lane order. -/
@[step] theorem append_nodes_spec {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (hasher : List U8) :
    lean_sphincs.hash.append_nodes hasher nodes ⦃ out =>
      out = hasher ++ nodes.val.flatMap (fun node => node.val) ⦄ := by
  unfold lean_sphincs.hash.append_nodes
  apply WP.spec_mono (loop_spec nodes hasher hasher 0#usize (by simp)
    (by simp [Writer.headBytes]))
  intro out hout
  simpa only [Writer.headBytes, ← nodes.property, List.take_length] using hout

end RustCrypto.AppendNodes
