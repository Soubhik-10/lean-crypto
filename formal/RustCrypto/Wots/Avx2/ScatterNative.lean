module
public import RustCrypto.Wots.Avx2.Scatter
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem native_set_read (nodes : Aeneas.Std.Array Node 16#usize) (index : Usize) (value : Node)
    (j : Nat) (hj : j < 16) : nativeNode ((nodes.set index value)[j]!) =
      if j = index.val then nativeNode value else nativeNode (nodes[j]!) := by
  rw [RustCrypto.BatchNodes.array_set_read nodes index value j hj]
  split <;> rfl

abbrev selected4 (chains : Aeneas.Std.Array Usize 4#usize) (j : Nat) : Prop :=
  j = (chains[0]!).val ∨ j = (chains[1]!).val ∨ j = (chains[2]!).val ∨ j = (chains[3]!).val

/-- Four source scatters implement a selected-index update, including repeated indices. -/
theorem scatter_four_native (nodes : Aeneas.Std.Array Node 16#usize) (chains : Aeneas.Std.Array Usize 4#usize)
    (values : Aeneas.Std.Array Node 4#usize) (f : Nat → EthLib.Cryptography.Sphincs.Digest)
    (hvalues : ∀ lane < 4, nativeNode (values[lane]!) = f (chains[lane]!).val) (j : Nat) (hj : j < 16) :
    nativeNode ((scatter chains values 4 0 nodes)[j]!) =
      if selected4 chains j then f j else nativeNode (nodes[j]!) := by
  have h0 := hvalues 0 (by decide)
  have h1 := hvalues 1 (by decide)
  have h2 := hvalues 2 (by decide)
  have h3 := hvalues 3 (by decide)
  simp (disch := omega) only [scatter,native_set_read]
  simp only [h0,h1,h2,h3]
  by_cases e0 : j = (chains[0]!).val <;>
    by_cases e1 : j = (chains[1]!).val <;>
    by_cases e2 : j = (chains[2]!).val <;>
    by_cases e3 : j = (chains[3]!).val <;>
    simp_all [selected4]

end RustCrypto.WotsAvx2
