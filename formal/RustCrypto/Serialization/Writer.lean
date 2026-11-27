module
public import LeanSphincs.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.Writer
abbrev Node := Aeneas.Std.Array U8 16#usize

def headBytes {N : Usize} (nodes : Aeneas.Std.Array Node N) (count : Nat) : List U8 :=
  (nodes.val.take count).flatMap fun node => node.val

theorem prefix_succ {N : Usize} (nodes : Aeneas.Std.Array Node N) (i : Nat)
    (hi : i < N.val) :
    headBytes nodes (i + 1) = headBytes nodes i ++ (nodes.val[i]'(by simpa using hi)).val := by
  unfold headBytes
  rw [List.take_succ_eq_append_getElem (show i < nodes.val.length by simpa using hi)]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem prefix_length {N : Usize} (nodes : Aeneas.Std.Array Node N) (i : Nat)
    (hi : i ≤ N.val) : (headBytes nodes i).length = i * 16 := by
  induction i with
  | zero => simp [headBytes]
  | succ i ih =>
    rw [prefix_succ nodes i (by omega)]
    simp [ih (by omega), Nat.add_mul]

theorem replace_after_prefix (headBytes tail bytes : List U8) (h : bytes.length ≤ tail.length) :
    (headBytes ++ tail).setSlice! headBytes.length bytes = headBytes ++ bytes ++ tail.drop bytes.length := by
  simp [List.setSlice!, List.drop_append, List.take_of_length_le,
    Nat.min_eq_left h, List.append_assoc]

@[step] theorem body_success {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (output : Slice U8) (i : Usize) (hi : i.val < N.val)
    (ho : i.val < output.val.length / 16) :
    lean_sphincs.signature.write_nodes_loop.body nodes output i ⦃ result =>
      match result with
      | .cont (out, next) => next.val = i.val + 1 ∧
          out.val = output.val.setSlice! (i.val * 16)
            (nodes.val[i.val]'(by simpa using hi)).val
      | .done _ => False ⦄ := by
  unfold lean_sphincs.signature.write_nodes_loop.body
  simp only [lean_sphincs.params.NODE_BYTES,
    alloy_primitives.bits.fixed.FixedBytes.as_slice]
  step*
  simp_all

@[step] theorem body_done {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (output : Slice U8) (i : Usize)
    (h : N.val ≤ i.val ∨ output.val.length / 16 ≤ i.val) :
    lean_sphincs.signature.write_nodes_loop.body nodes output i ⦃ result =>
      result = .done output ⦄ := by
  unfold lean_sphincs.signature.write_nodes_loop.body
  simp only [lean_sphincs.params.NODE_BYTES]
  by_cases hi : i < N
  · simp only [ite_eq_left hi]
    step as ⟨q, hq⟩
    have hstop : ¬ i < q := by scalar_tac
    simp [hstop, WP.spec_ok]
  · simp [hi, WP.spec_ok]

def invariant {N : Usize} (nodes : Aeneas.Std.Array Node N) (original : Slice U8)
    (state : Slice U8 × Usize) : Prop :=
  state.2.val ≤ N.val ∧ state.2.val ≤ original.val.length / 16 ∧
    state.1.val = headBytes nodes state.2.val ++ original.val.drop (state.2.val * 16)

theorem invariant_length {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (original : Slice U8) (state : Slice U8 × Usize) (h : invariant nodes original state) :
    state.1.val.length = original.val.length := by
  rcases h with ⟨hn, ho, heq⟩
  rw [heq, List.length_append, prefix_length nodes _ hn, List.length_drop]
  omega

/-- The loop always terminates and writes precisely the available complete nodes. -/
@[step] theorem loop_spec {N : Usize} (nodes : Aeneas.Std.Array Node N)
    (original output : Slice U8) (i : Usize) (hinv : invariant nodes original (output, i)) :
    lean_sphincs.signature.write_nodes_loop output nodes i ⦃ out =>
      let count := min N.val (original.val.length / 16)
      out.val = headBytes nodes count ++ original.val.drop (count * 16) ⦄ := by
  let count := min N.val (original.val.length / 16)
  unfold lean_sphincs.signature.write_nodes_loop
  apply loop.spec_decr_nat
    (fun state : Slice U8 × Usize => count - state.2.val)
    (invariant nodes original)
  · rintro ⟨out, j⟩ h
    have hlen := invariant_length nodes original (out, j) h
    rcases h with ⟨hjn, hjo, hbytes⟩
    dsimp only at hlen hjn hjo hbytes
    by_cases hrun : j.val < count
    · have hjnlt : j.val < N.val := by simp only [count] at hrun; omega
      have hjolt : j.val < out.val.length / 16 := by simp only [count] at hrun; omega
      apply WP.spec_mono (body_success nodes out j hjnlt hjolt)
      intro result hr
      cases result with
      | done value => exact False.elim hr
      | cont state =>
        rcases state with ⟨nextOut, nextJ⟩
        rcases hr with ⟨hnext, hwrite⟩
        have hp := prefix_length nodes j.val hjn
        have hroom : (nodes.val[j.val]'(by simpa using hjnlt)).val.length ≤
            (original.val.drop (j.val * 16)).length := by
          have hnlen : (nodes.val[j.val]'(by simpa using hjnlt)).val.length = 16 := by simp
          simp only [List.length_drop, hnlen]
          omega
        have hreplace := replace_after_prefix (headBytes nodes j.val)
          (original.val.drop (j.val * 16)) (nodes.val[j.val]'(by simpa using hjnlt)).val hroom
        have updated : nextOut.val = headBytes nodes (j.val + 1) ++
            original.val.drop ((j.val + 1) * 16) := by
          calc
            nextOut.val = (headBytes nodes j.val ++ original.val.drop (j.val * 16)).setSlice!
                (headBytes nodes j.val).length (nodes.val[j.val]'(by simpa using hjnlt)).val := by
              rw [hwrite, hbytes, hp]
            _ = _ := by
              rw [hreplace, prefix_succ nodes j.val hjnlt]
              simp [List.drop_drop, List.append_assoc, Nat.add_mul]
        constructor
        · dsimp [invariant]
          rw [hnext]
          exact ⟨by simp only [count] at hrun; omega, by simp only [count] at hrun; omega, updated⟩
        · dsimp
          rw [hnext]
          omega
    · have hstop : N.val ≤ j.val ∨ out.val.length / 16 ≤ j.val := by
        simp only [count] at hrun
        omega
      apply WP.spec_mono (body_done nodes out j hstop)
      intro result hr
      subst result
      have heq : j.val = count := by simp only [count] at *; omega
      simpa only [heq] using hbytes
  · exact hinv

/-- Complete source writer contract, including zero nodes and partial output tails. -/
@[step] theorem write_nodes_spec {N : Usize} (nodes : Aeneas.Std.Array Node N) (output : Slice U8) :
    lean_sphincs.signature.write_nodes output nodes ⦃ out =>
      let count := min N.val (output.val.length / 16)
      out.val = headBytes nodes count ++ output.val.drop (count * 16) ⦄ := by
  unfold lean_sphincs.signature.write_nodes
  exact loop_spec nodes output output 0#usize (by simp [invariant, headBytes])

end RustCrypto.Writer
