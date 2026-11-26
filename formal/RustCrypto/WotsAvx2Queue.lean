module
public import RustCrypto.WotsAvx2ScatterNative
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

/-- Membership in the live prefix of the source batching queue. -/
def queued (chains : Aeneas.Std.Array Usize 4#usize) (count j : Nat) : Prop :=
  ∃ lane < count, lane < 4 ∧ j = (chains[lane]!).val

noncomputable instance (chains : Aeneas.Std.Array Usize 4#usize) (count j : Nat) : Decidable (queued chains count j) :=
  Classical.propDecidable _

theorem queued_zero (chains : Aeneas.Std.Array Usize 4#usize) (j : Nat) : ¬queued chains 0 j := by
  rintro ⟨lane,h,_⟩
  omega

theorem queued_four (chains : Aeneas.Std.Array Usize 4#usize) (j : Nat) :
    queued chains 4 j ↔ selected4 chains j := by
  constructor
  · rintro ⟨lane,hlane,_,h⟩
    have hc : lane = 0 ∨ lane = 1 ∨ lane = 2 ∨ lane = 3 := by omega
    rcases hc with rfl|rfl|rfl|rfl <;> simp_all [selected4]
  · intro h
    rcases h with h|h|h|h
    · exact ⟨0,by decide,by decide,h⟩
    · exact ⟨1,by decide,by decide,h⟩
    · exact ⟨2,by decide,by decide,h⟩
    · exact ⟨3,by decide,by decide,h⟩

theorem queued_append (chains : Aeneas.Std.Array Usize 4#usize) (count chain : Usize)
    (hcount : count.val < 4) (j : Nat) :
    queued (chains.set count chain) (count.val+1) j ↔ queued chains count.val j ∨ j = chain.val := by
  constructor
  · rintro ⟨lane,hlane,hfour,hj⟩
    rw [RustCrypto.BatchNodes.array_set_read chains count chain lane hfour] at hj
    by_cases heq : lane = count.val
    · exact Or.inr (by simpa only [ite_eq_left heq] using hj)
    · left
      refine ⟨lane,by omega,hfour,?_⟩
      simpa only [ite_eq_right heq] using hj
  · rintro (h|h)
    · rcases h with ⟨lane,hlane,hfour,hj⟩
      refine ⟨lane,by omega,hfour,?_⟩
      rw [RustCrypto.BatchNodes.array_set_read chains count chain lane hfour,ite_eq_right (by omega)]
      exact hj
    · refine ⟨count.val,by omega,hcount,?_⟩
      rw [RustCrypto.BatchNodes.array_set_read chains count chain count.val hcount,ite_eq_left rfl]
      exact h

theorem append_bounded (chains : Aeneas.Std.Array Usize 4#usize) (count chain : Usize)
    (_hcount : count.val < 4) (hchain : chain.val < 16)
    (hchains : ∀ j < 4, (chains[j]!).val < 16) :
    ∀ j < 4, ((chains.set count chain)[j]!).val < 16 := by
  intro j hj
  rw [RustCrypto.BatchNodes.array_set_read chains count chain j hj]
  split
  · exact hchain
  · exact hchains j hj

end RustCrypto.WotsAvx2
