module
public import RustCrypto.Wots.Avx2.Queue
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
set_option maxHeartbeats 300000

/-- Live queued indices are distinct because the source scans chains in increasing order. -/
def queueDistinct (chains : Aeneas.Std.Array Usize 4#usize) (count : Nat) : Prop :=
  ∀ a < count, ∀ b < count, (chains[a]!).val = (chains[b]!).val → a = b

theorem queue_distinct_zero (chains : Aeneas.Std.Array Usize 4#usize) : queueDistinct chains 0 := by
  intro a ha
  omega

theorem queue_distinct_append (chains : Aeneas.Std.Array Usize 4#usize) (count scanned : Usize)
    (hcount : count.val < 4) (hdistinct : queueDistinct chains count.val)
    (hbefore : ∀ j, queued chains count.val j → j < scanned.val) :
    queueDistinct (chains.set count scanned) (count.val+1) := by
  intro a ha b hb heq
  rw [RustCrypto.BatchNodes.array_set_read chains count scanned a (show a < 4 by omega),
      RustCrypto.BatchNodes.array_set_read chains count scanned b (show b < 4 by omega)] at heq
  by_cases ea : a = count.val
  · by_cases eb : b = count.val
    · omega
    · have hb' : b < count.val := by omega
      have hbelow := hbefore (chains[b]!).val ⟨b,hb',by omega,rfl⟩
      simp only [ite_eq_left ea,ite_eq_right eb] at heq
      omega
  · by_cases eb : b = count.val
    · have ha' : a < count.val := by omega
      have hbelow := hbefore (chains[a]!).val ⟨a,ha',by omega,rfl⟩
      simp only [ite_eq_right ea,ite_eq_left eb] at heq
      omega
    · simp only [ite_eq_right ea,ite_eq_right eb] at heq
      exact hdistinct a (by omega) b (by omega) heq

theorem queued_succ (chains : Aeneas.Std.Array Usize 4#usize) (count j : Nat) (hcount : count < 4) :
    queued chains (count+1) j ↔ queued chains count j ∨ j = (chains[count]!).val := by
  constructor
  · rintro ⟨lane,hlane,hfour,heq⟩
    by_cases h : lane < count
    · exact Or.inl ⟨lane,h,hfour,heq⟩
    · have he : lane = count := by omega
      exact Or.inr (he ▸ heq)
  · rintro (h|h)
    · rcases h with ⟨lane,hlane,hfour,heq⟩
      exact ⟨lane,by omega,hfour,heq⟩
    · exact ⟨count,by omega,hcount,h⟩

theorem not_queued_future (chains : Aeneas.Std.Array Usize 4#usize) (count tail lane : Nat)
    (htail : tail ≤ lane) (hlane : lane < count) (hdistinct : queueDistinct chains count) :
    ¬queued chains tail (chains[lane]!).val := by
  rintro ⟨earlier,hearlier,_,heq⟩
  have he := hdistinct lane hlane earlier (by omega) heq
  omega

end RustCrypto.WotsAvx2
