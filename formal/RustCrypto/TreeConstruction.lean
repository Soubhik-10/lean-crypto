module
public import RustCrypto.ConstructorPath
public import RustCrypto.SecretBridge
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.BuildRoot
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.TreePrimitives RustCrypto.WotsEthlib
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def builtPathList (tree : EthLib.Cryptography.Merkle.Built α) (height target : Nat) : List α :=
  (tree.path height target).toList

@[step] theorem build_fors_path_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (target : U32) (path : Slice Node)
    (htarget : target.val < 1024) (hlen : path.val.length = 10)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.build_tree address secret
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf))
      10#u32 target path ⦃ out =>
      out.2.2.val.map nativeNode =
        ((EthLib.Cryptography.Sphincs.forsBuild EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
          (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa).path
            10 target.val).toList ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  let model := forsModel seed secret idx kappa
  let kind := lean_sphincs.tree.TreeKind.Fors (stepWord kappa.val)
    (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)
  have hsource := build_tree_path_ethlib_spec model secret kind
    (fors_leaf_contract seed secret idx kappa) (fors_parent_contract seed secret idx kappa)
    address 10#u32 target path (by decide) htarget hlen hframe
  have hten : (10#u32).val = 10 := rfl
  apply WP.spec_mono hsource
  intro out hout
  constructor
  · have hp := hout.1
    change out.2.2.val.map nativeNode = builtPathList
      (EthLib.Cryptography.Merkle.build (m := Id) model.parent model.leaf ⟨(10#u32).val,0⟩) (10#u32).val target.val at hp
    rw [hten] at hp
    simpa only [builtPathList,model,forsModel,EthLib.Cryptography.Sphincs.forsBuild,
      EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT] using hp
  · exact hout.2

/-- The actual FORS constructor returns EthLib's entire tree opening and root. -/
@[step] theorem build_fors_opening_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (target : U32) (path : Slice Node)
    (htarget : target.val < 1024) (hlen : path.val.length = 10)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.build_tree address secret
      (.Fors (stepWord kappa.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf))
      10#u32 target path ⦃ out =>
      let reference := EthLib.Cryptography.Sphincs.treeOpen EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
        idx kappa ⟨target.val,htarget⟩
      nativeNode out.1.1 = reference.2 ∧ nativeNode out.1.2 = reference.1.secret ∧
      out.2.2.val.map nativeNode = reference.1.path.toList ∧
      TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ⦄ := by
  have hsource := WP.spec_and (build_fors_root_ethlib_spec address seed secret idx kappa target path hframe)
    (WP.spec_and (build_fors_secret_ethlib_spec address seed secret idx kappa target path htarget hframe)
      (build_fors_path_ethlib_spec address seed secret idx kappa target path htarget hlen hframe))
  have hrootValue :
      (EthLib.Cryptography.Sphincs.forsBuild EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa).value =
      EthLib.Cryptography.Sphincs.forsRoot EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa := by
    simpa only [EthLib.Cryptography.Sphincs.forsBuild,EthLib.Cryptography.Sphincs.forsRoot,
      EthLib.Cryptography.Merkle.root,EthLib.Cryptography.Merkle.node] using
      RustCrypto.MerklePath.build_value
        (EthLib.Cryptography.Sphincs.forsNodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) idx kappa)
        (EthLib.Cryptography.Sphincs.forsLeaves EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
          (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa)
        EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT 0
  apply WP.spec_mono hsource
  rintro out ⟨⟨hroot,hnext⟩,⟨⟨hsecret,_⟩,⟨hpath,_⟩⟩⟩
  simp only [EthLib.Cryptography.Sphincs.treeOpen,Bind.bind,Pure.pure]
  exact ⟨hroot.trans hrootValue.symm,hsecret,hpath,hnext⟩

@[step] theorem build_xmss_path_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (height target : U32) (path : Slice Node) (hheight : height.val = layer.height)
    (htarget : target.val < 2^height.val) (hlen : path.val.length = height.val)
    (hframe : TreePrimitives.frame address seed layer tree) :
    lean_sphincs.tree.build_xmss address secret height target path ⦃ out =>
      out.2.2.val.map nativeNode =
        ((EthLib.Cryptography.Sphincs.buildTree EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
          (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) layer tree).path
            layer.height target.val).toList ∧ TreePrimitives.frame out.2.1 seed layer tree ⦄ := by
  have hh : height.val ≤ 10 := by rw [hheight]; cases layer <;> decide
  let model := xmssModel seed secret layer tree
  have hsource := build_tree_path_ethlib_spec model secret .Xmss
    (xmss_leaf_contract seed secret layer tree) (xmss_parent_contract seed secret layer tree)
    address height target path hh htarget hlen hframe
  unfold lean_sphincs.tree.build_xmss
  step with hsource as ⟨pair,next,remaining,hpath,hnext⟩
  rcases pair with ⟨root,selected⟩
  simp only [Aeneas.Std.uncurry,WP.spec_ok]
  constructor
  · change remaining.val.map nativeNode = builtPathList
      (EthLib.Cryptography.Merkle.build (m := Id) model.parent model.leaf ⟨height.val,0⟩) height.val target.val at hpath
    rw [hheight] at hpath
    simpa only [builtPathList,model,xmssModel,EthLib.Cryptography.Sphincs.buildTree] using hpath
  · exact hnext

/-- Actual XMSS construction returns the reference built tree's root and full path. -/
@[step] theorem build_xmss_opening_ethlib_spec (address : Address) (seed : Node)
    (secret : Aeneas.Std.Array U8 32#usize) (layer : EthLib.Cryptography.Sphincs.Layer) (tree : Nat)
    (height target : U32) (path : Slice Node) (hheight : height.val = layer.height)
    (htarget : target.val < 2^height.val) (hlen : path.val.length = height.val)
    (hframe : TreePrimitives.frame address seed layer tree) :
    lean_sphincs.tree.build_xmss address secret height target path ⦃ out =>
      let reference := EthLib.Cryptography.Sphincs.buildTree EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) layer tree
      nativeNode out.1 = reference.value ∧ out.2.2.val.map nativeNode = (reference.path layer.height target.val).toList ∧
      TreePrimitives.frame out.2.1 seed layer tree ⦄ := by
  have hsource := WP.spec_and (build_xmss_root_ethlib_spec address seed secret layer tree height target path hheight hframe)
    (build_xmss_path_ethlib_spec address seed secret layer tree height target path hheight htarget hlen hframe)
  have hrootValue :
      (EthLib.Cryptography.Sphincs.buildTree EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) layer tree).value =
      EthLib.Cryptography.Sphincs.treeRoot EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
        (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) layer tree := by
    simpa only [EthLib.Cryptography.Sphincs.buildTree,EthLib.Cryptography.Sphincs.treeRoot,
      EthLib.Cryptography.Merkle.root,EthLib.Cryptography.Merkle.node] using
      RustCrypto.MerklePath.build_value
        (EthLib.Cryptography.Sphincs.nodeHash EthLib.Cryptography.Sphincs.hashId (nativeNode seed) layer tree)
        (EthLib.Cryptography.Sphincs.leaves EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
          (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) layer tree)
        layer.height 0
  apply WP.spec_mono hsource
  rintro out ⟨⟨hroot,hnext⟩,⟨hpath,_⟩⟩
  exact ⟨hroot.trans hrootValue.symm,hpath,hnext⟩

end RustCrypto.BuildRoot
