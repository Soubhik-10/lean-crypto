module
public import RustCrypto.TopCacheModel
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.TopCache
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem width_previous (height : Nat) (hpos : 0 < height) (hheight : height ≤ 10) :
    width (height-1) = 2*width height := by
  have hs := width_succ (height-1) (by omega)
  have he : height-1+1 = height := by omega
  simpa only [he] using hs

theorem parent_width_bound (height : Nat) (hpos : 0 < height) (hheight : height ≤ 10) : width height ≤ 512 := by
  have hp := width_previous height hpos hheight
  have hb := width_bounded (height-1)
  omega

/-- A parent write is below every completed lower-level cache region. -/
theorem update_preserves_lower (nodes : Nodes) (root seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (height index level : Nat) (slot : Usize) (hpos : 0 < height) (hheight : height ≤ 10)
    (hindex : index < width height) (hlevel : level < height) (hslot : slot.val = width height+index)
    (hvalid : levelValid nodes seed secret level) : levelValid (nodes.set slot root) seed secret level := by
  intro j hj
  have hb := width_bounded level
  have hprev := width_previous height hpos hheight
  have hmono := width_antitone level (height-1) (by omega)
  have hneq : width level+j ≠ slot.val := by omega
  rw [array_set_read nodes slot root (width level+j) (show width level+j < 2048 by omega),ite_eq_right hneq]
  exact hvalid j hj

/-- Both cached children are the canonical nodes for the next parent. -/
theorem cached_parent_value (nodes : Nodes) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (height index : Nat) (hpos : 0 < height) (hheight : height ≤ 10) (hindex : index < width height)
    (hlower : ∀ level < height, levelValid nodes seed secret level) :
    EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) .top 0 ⟨height,index⟩
      (nativeNode (nodes[2*(width height+index)]!)) (nativeNode (nodes[2*(width height+index)+1]!)) =
      value seed secret height index := by
  have hp := width_previous height hpos hheight
  have hl : nativeNode (nodes[2*(width height+index)]!) = value seed secret (height-1) (2*index) := by
    have he : 2*(width height+index) = width (height-1)+2*index := by omega
    rw [he]
    exact hlower (height-1) (by omega) (2*index) (by omega)
  have hr : nativeNode (nodes[2*(width height+index)+1]!) = value seed secret (height-1) (2*index+1) := by
    have he : 2*(width height+index)+1 = width (height-1)+(2*index+1) := by omega
    rw [he]
    exact hlower (height-1) (by omega) (2*index+1) (by omega)
  rw [hl,hr]
  have he : height-1+1 = height := by omega
  simpa only [he] using (value_succ seed secret (height-1) index).symm

end RustCrypto.TopCache
