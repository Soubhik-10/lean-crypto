module
public import RustCrypto.Fors.Scalar.Bytes
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ClimbBridge
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.Climb RustCrypto.WotsEthlib
open RustCrypto.ForsRead
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem recover_key_failure (nodes : List Node) (tail : List U8) (address : Address) (reader : Slice U8)
    (seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (kind : EthLib.Cryptography.Sphincs.AdrsType)
    (fuel level : Nat) (position : U32) (node : Node) (hshort : nodes.length < fuel)
    (hbound : level+fuel < 4294967296) (htail : tail.length < 16)
    (hframe : keyFrame address seed key kind) (hreader : reader.val = nodesBytes nodes ++ tail) :
    ∃ next remaining, recover fuel level address reader position node = (none,next,remaining) ∧
      remaining.val = tail ∧ keyFrame next seed key kind := by
  induction nodes generalizing address reader fuel level position node with
  | nil =>
    cases fuel with
    | zero => simp only [List.length_nil] at hshort; omega
    | succ fuel =>
      have hr : reader.val = tail := by simpa only [nodesBytes,List.flatMap_nil,List.nil_append] using hreader
      have hread : ¬16 ≤ reader.val.length := by rw [hr]; omega
      let nextAddress := positioned address (stepWord (level+1)) (halfPosition position)
      rcases hframe with ⟨old2,old3,hhead⟩
      have hp := positioned_frame address seed (stepWord key.layer.toNat) (treeWord key.tree)
        (addressTag kind) (stepWord key.leaf) old2 old3 (stepWord (level+1)) (halfPosition position) hhead
      refine ⟨nextAddress,reader,?_,hr,stepWord (level+1),halfPosition position,hp⟩
      simp only [recover,dite_eq_right hread,nextAddress]
  | cons sibling rest ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at hshort; omega
    | succ fuel =>
      have hread : 16 ≤ reader.val.length := by
        rw [hreader]
        simp only [nodesBytes,List.flatMap_cons,List.length_append]
        have hl : sibling.val.length = 16 := by simp
        omega
      have hsize : (16#usize).val = 16 := rfl
      have hprefix : RustParser.readPrefix 16#usize reader hread = sibling := by
        apply Aeneas.Std.Array.ext
        simp only [RustParser.readPrefix,Aeneas.Std.Array.from_val,hreader,nodesBytes,List.flatMap_cons,hsize,List.append_assoc]
        have hl : sibling.val.length = 16 := by simp
        have ht : sibling.val.take 16 = sibling.val := List.take_of_length_le (by omega)
        simp only [List.take_append,ht,hl,Nat.sub_self,Nat.zero_sub,List.take_zero,List.append_nil]
      have hsuffix : (RustParser.readSuffix 16#usize reader).val = nodesBytes rest ++ tail := by
        simp only [RustParser.readSuffix,Slice.from_val,hreader,nodesBytes,List.flatMap_cons,hsize,List.append_assoc]
        have hl : sibling.val.length = 16 := by simp
        have hd : sibling.val.drop 16 = [] := List.drop_eq_nil_iff.mpr (by omega)
        simp only [List.drop_append,hd,hl,Nat.sub_self,Nat.zero_sub,List.drop_zero,List.nil_append]
      have hstep := parent_step_key address seed key kind level position node sibling (by omega) hframe
      let next := parentStep (positioned address (stepWord (level+1)) (halfPosition position)) position node sibling
      rcases ih next.2 (RustParser.readSuffix 16#usize reader) fuel (level+1) (halfPosition position) next.1
        (by simp only [List.length_cons] at hshort; omega) (by omega) hstep.2 hsuffix with
        ⟨finalAddress,remaining,hresult,hremaining,hfinal⟩
      refine ⟨finalAddress,remaining,?_,hremaining,hfinal⟩
      simp only [recover,dite_eq_left hread,hprefix]
      exact hresult

/-- Every truncated authentication path returns `None`, retains its address frame and leaves the incomplete node. -/
@[step] theorem climb_key_short_spec (address : Address) (reader : Slice U8) (position height : U32)
    (node seed : Node) (key : EthLib.Cryptography.Sphincs.OtsKey) (kind : EthLib.Cryptography.Sphincs.AdrsType)
    (hheight : height.val ≤ 10) (hshort : reader.val.length < 16*height.val)
    (hframe : keyFrame address seed key kind) :
    lean_sphincs.tree.climb address reader position height node ⦃ out =>
      out.1 = none ∧ out.2.2.val = reader.val.drop (16*(reader.val.length/16)) ∧ keyFrame out.2.1 seed key kind ⦄ := by
  let count := reader.val.length/16
  let nodes := nodeList reader.val count 0
  let tail := reader.val.drop (16*count)
  have hroom : 16*count ≤ reader.val.length := by dsimp only [count]; omega
  have hnodes : nodes.length < height.val := by simp only [nodes,nodeList_length]; dsimp only [count]; omega
  have htail : tail.length < 16 := by simp only [tail,List.length_drop]; dsimp only [count]; omega
  have hreader : reader.val = nodesBytes nodes ++ tail := by
    rw [serialized_nodes reader.val count 0 (by omega)]
    simp only [List.drop_zero]
    exact (List.take_append_drop (16*count) reader.val).symm
  rcases recover_key_failure nodes tail address reader seed key kind height.val 0 position node hnodes
    (by omega) htail hframe hreader with ⟨next,remaining,hresult,hremaining,hnext⟩
  apply WP.spec_mono (RustCrypto.Climb.climb_spec address reader position height node)
  intro out hout
  rw [hout,hresult]
  exact ⟨rfl,hremaining,hnext⟩

end RustCrypto.ClimbBridge
