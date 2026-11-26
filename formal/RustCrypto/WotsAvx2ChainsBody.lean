module
public import RustCrypto.WotsAvx2Window
public import RustCrypto.WotsAvx2ReadFull
public import RustCrypto.WotsAvx2Prefix
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.WotsAvx2
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge RustCrypto.ForsRead
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

@[step] theorem chains_body_spec (address : Address) (reader : Slice U8) (ends : List U8)
    (addresses : Aeneas.Std.Array Address 4#usize) (digits : WotsRecover.Digits)
    (word : EthLib.Cryptography.Sphincs.Codeword) (window : Usize)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hwindow : window.val < 4) (hreader : 256 ≤ reader.val.length)
    (hdigits : WotsRecover.digitRelation digits word) (hframe : keyFrame address seed key .wotsHash)
    (hframes : ∀ j < 4, keyFrame (addresses[j]!) seed key .wotsHash) :
    lean_sphincs.wots.recover_chains_loop.body digits address reader ends addresses window ⦃ out =>
      match out with
      | .done _ => False
      | .cont (nextAddress,nextReader,nextEnds,nextAddresses,nextWindow) =>
          nextWindow.val = window.val+1 ∧ nextReader.val = reader.val.drop 256 ∧
          keyFrame nextAddress seed key .wotsHash ∧
          (∀ j < 4, keyFrame (nextAddresses[j]!) seed key .wotsHash) ∧
          ∃ roots : Aeneas.Std.Array Node 16#usize,
            nextEnds = ends ++ roots.val.flatMap (fun root => root.val) ∧
            ∀ (j : Nat) (hj : j < 16), nativeNode (roots[j]!) = WotsRecover.endValue seed key word
              ⟨16*window.val+j,by change 16*window.val+j < 64; omega⟩ (nativeNode (ForsRead.nodeAt reader.val (16*j))) ⦄ := by
  unfold lean_sphincs.wots.recover_chains_loop.body
  simp only [lean_sphincs.params.WOTS_CHAINS,lean_sphincs.wots.CHAINS_PER_WINDOW]
  step as ⟨bound,hbound⟩
  have hb : bound.val = 4 := by scalar_tac
  have hrun : window < bound := by scalar_tac
  simp only [ite_eq_left hrun]
  step as ⟨offset,hoffset⟩
  have ho : offset.val = 16*window.val := by scalar_tac
  step with read_window_spec reader hreader as ⟨option,nextReader,hoption,hnextReader⟩
  rw [hoption]
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_ok]
  step with recover_window_ethlib_spec address addresses (windowNodes reader.val) digits word offset seed key
    (by omega) hdigits hframe hframes as ⟨roots,nextAddress,nextAddresses,hnextFrame,hnextFrames,hroots⟩
  step with RustCrypto.AppendNodes.append_nodes_spec roots ends as ⟨nextEnds,hnextEnds⟩
  step as ⟨nextWindow,hnextWindow⟩
  refine ⟨hnextWindow,hnextReader,hnextFrame,hnextFrames,roots,hnextEnds,?_⟩
  intro j hj
  simpa only [ho,window_get reader.val j hj] using hroots j hj

end RustCrypto.WotsAvx2
