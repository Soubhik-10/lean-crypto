module
public import RustCrypto.ForsBatchWalk
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsBatch
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.ClimbBridge
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def pathNodes (opening : Aeneas.Std.Array U8 176#usize) : Nat → Nat → List Node
  | 0,_ => []
  | fuel+1,level => readNode opening (level+1) :: pathNodes opening fuel (level+1)

@[simp] theorem pathNodes_length (opening : Aeneas.Std.Array U8 176#usize) (fuel level : Nat) :
    (pathNodes opening fuel level).length = fuel := by
  induction fuel generalizing level with
  | zero => rfl
  | succ fuel ih => simp only [pathNodes,List.length_cons,ih]

/-- The lane model is EthLib's addressed Merkle climb, with the address frame retained. -/
theorem walk_native (opening : Aeneas.Std.Array U8 176#usize) (fuel level : Nat)
    (position : U32) (node : Node) (address : Address) (seed : Node)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (kind : EthLib.Cryptography.Sphincs.AdrsType)
    (hbound : level+fuel ≤ 10) (hframe : keyFrame address seed key kind) :
    nativeNode (walk opening fuel level position node address).1 =
      EthLib.Cryptography.Merkle.climb (keyNodeHash (nativeNode seed) key kind) ⟨level,position.val⟩
        (nativeNode node) ((pathNodes opening fuel level).map nativeNode) ∧
    keyFrame (walk opening fuel level position node address).2 seed key kind := by
  induction fuel generalizing level position node address with
  | zero => exact ⟨rfl,hframe⟩
  | succ fuel ih =>
    have hstep := parent_step_key address seed key kind level position node (readNode opening (level+1))
      (by omega) hframe
    let next := RustCrypto.Climb.parentStep
      (positioned address (stepWord (level+1)) (RustCrypto.Climb.halfPosition position))
      position node (readNode opening (level+1))
    have hrec := ih (level+1) (RustCrypto.Climb.halfPosition position) next.1 next.2 (by omega) hstep.2
    constructor
    · rw [walk]
      rw [hrec.1]
      simp only [pathNodes,List.map_cons,EthLib.Cryptography.Merkle.climb,
        EthLib.Cryptography.Merkle.Position.parent,half_position_val,Bind.bind]
      rw [hstep.1]
    · exact hrec.2

end RustCrypto.ForsBatch
