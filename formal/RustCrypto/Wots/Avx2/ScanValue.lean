module
public import RustCrypto.Wots.Avx2.Queue
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
set_option maxHeartbeats 300000

noncomputable def scanValue {T : Type} (active : Nat → Prop) (base hashed : Nat → T)
    (chains : Aeneas.Std.Array Usize 4#usize) (count scanned j : Nat) : T :=
  by
    classical
    exact if j < scanned ∧ active j ∧ ¬queued chains count j then hashed j else base j

theorem scan_value_waiting {T : Type} (active : Nat → Prop) (base hashed : Nat → T)
    (chains : Aeneas.Std.Array Usize 4#usize) (count scanned j : Nat)
    (h : queued chains count j ∨ j = scanned) :
    scanValue active base hashed chains count scanned j = base j := by
  classical
  unfold scanValue
  apply ite_eq_right
  rcases h with h|rfl
  · tauto
  · omega

theorem scan_value_skip {T : Type} (active : Nat → Prop) (base hashed : Nat → T)
    (chains : Aeneas.Std.Array Usize 4#usize) (count scanned : Nat) (hinactive : ¬active scanned) (j : Nat) :
    scanValue active base hashed chains count (scanned+1) j =
      scanValue active base hashed chains count scanned j := by
  classical
  unfold scanValue
  congr 1
  apply propext
  constructor
  · rintro ⟨hj,ha,hq⟩
    have hlt : j < scanned := by
      by_contra h
      have he : j = scanned := by omega
      exact hinactive (he ▸ ha)
    exact ⟨hlt,ha,hq⟩
  · rintro ⟨hj,ha,hq⟩
    exact ⟨by omega,ha,hq⟩

theorem scan_value_enqueue {T : Type} (active : Nat → Prop) (base hashed : Nat → T)
    (chains : Aeneas.Std.Array Usize 4#usize) (count scanned : Usize) (hcount : count.val < 4) (j : Nat) :
    scanValue active base hashed (chains.set count scanned) (count.val+1) (scanned.val+1) j =
      scanValue active base hashed chains count.val scanned.val j := by
  classical
  unfold scanValue
  simp only [queued_append chains count scanned hcount j]
  congr 1
  apply propext
  constructor
  · rintro ⟨hj,ha,hq⟩
    exact ⟨by omega,ha,by tauto⟩
  · rintro ⟨hj,ha,hq⟩
    exact ⟨by omega,ha,by rintro (h|h); exact hq h; omega⟩

theorem scan_value_flush {T : Type} (active : Nat → Prop) (base hashed : Nat → T)
    (chains : Aeneas.Std.Array Usize 4#usize) (count scanned : Usize) (hcount : count.val < 4)
    (hfull : count.val+1 = 4) (hactive : active scanned.val)
    (hqueued : ∀ j, queued chains count.val j → j < scanned.val ∧ active j) (j : Nat) :
    (if selected4 (chains.set count scanned) j then hashed j
     else scanValue active base hashed chains count.val scanned.val j) =
      scanValue active base hashed (chains.set count scanned) 0 (scanned.val+1) j := by
  classical
  have hselected : selected4 (chains.set count scanned) j ↔ queued chains count.val j ∨ j = scanned.val := by
    exact (queued_four (chains.set count scanned) j).symm.trans
      (by simpa only [hfull] using queued_append chains count scanned hcount j)
  unfold scanValue
  simp only [queued_zero,not_false_eq_true,and_true]
  by_cases hq : queued chains count.val j
  · have hb := hqueued j hq
    have hs : selected4 (chains.set count scanned) j := hselected.mpr (Or.inl hq)
    simp only [ite_eq_left hs,ite_eq_left (show j < scanned.val+1 ∧ active j from ⟨by omega,hb.2⟩)]
  · by_cases heq : j = scanned.val
    · have hs : selected4 (chains.set count scanned) j := hselected.mpr (Or.inr heq)
      rw [ite_eq_left hs]
      apply Eq.symm
      apply ite_eq_left
      exact ⟨by omega,heq.symm ▸ hactive⟩
    · have hs : ¬selected4 (chains.set count scanned) j := by rw [hselected]; tauto
      have hcut : j < scanned.val+1 ↔ j < scanned.val := by omega
      simp only [ite_eq_right hs,hq,not_false_eq_true,and_true,hcut]

end RustCrypto.WotsAvx2
