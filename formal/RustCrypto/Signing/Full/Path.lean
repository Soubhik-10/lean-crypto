module
public import RustCrypto.Signing.Full.Wots
public import RustCrypto.Tree.Construction
public import RustCrypto.Tree.Cache.Path
public import RustCrypto.Serialization.Writer
public import RustCrypto.Common.OrderedPrefix
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.FullSign
open RustCrypto.WotsChain RustCrypto.AddressBridge RustCrypto.TweakableBridge RustCrypto.WotsEthlib
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

@[irreducible] def pathValues (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) : Vector EthLib.Cryptography.Sphincs.Digest key.layer.height :=
  EthLib.Cryptography.Sphincs.path EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
    key.layer key.tree key.leaf

@[irreducible] def pathBytes (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) : List UInt8 := (pathValues seed secret key).toList.flatMap Vector.toList

theorem built_path_canonical (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) (hleaf : key.leaf < 2^key.layer.height) :
    ((EthLib.Cryptography.Sphincs.buildTree EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
      key.layer key.tree).path key.layer.height key.leaf).toList = (pathValues seed secret key).toList := by
  unfold pathValues EthLib.Cryptography.Sphincs.buildTree EthLib.Cryptography.Sphincs.path EthLib.Cryptography.Merkle.path
  rw [RustCrypto.MerklePath.build_path_list _ _ key.layer.height 0 key.leaf (Nat.div_eq_of_lt hleaf),
    RustCrypto.MerklePath.siblings_list]
  simp only [Nat.zero_add]

theorem path_bytes_length (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (key : EthLib.Cryptography.Sphincs.OtsKey) : (pathBytes seed secret key).length = 16*key.layer.height := by
  unfold pathBytes
  have h := OrderedPrefix.prefix_length (pathValues seed secret key) Vector.toList 16
    (by intro row; exact Vector.length_toList) key.layer.height (by omega)
  rw [OrderedPrefix.prefix_full] at h
  omega

@[step] theorem write_path_spec (path : Aeneas.Std.Array Node 10#usize) (output : Slice U8)
    (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (key : EthLib.Cryptography.Sphincs.OtsKey)
    (hsize : output.val.length = 16*key.layer.height) (hheight : key.layer.height ≤ 10)
    (hpath : (path.val.take key.layer.height).map nativeNode = (pathValues seed secret key).toList) :
    lean_sphincs.signature.write_nodes output path ⦃ out => nativeBytes out.val = pathBytes seed secret key ⦄ := by
  apply WP.spec_mono (RustCrypto.Writer.write_nodes_spec path output)
  intro out hout
  have hcount : min (10#usize).val (output.val.length/16) = key.layer.height := by
    change min 10 (output.val.length/16) = key.layer.height
    rw [hsize]
    omega
  rw [hcount] at hout
  have hdrop : output.val.drop (key.layer.height*16) = [] := by apply List.drop_eq_nil_iff.mpr; omega
  rw [hout,hdrop,List.append_nil]
  unfold nativeBytes RustCrypto.Writer.headBytes pathBytes
  have hf := congrArg (List.flatMap Vector.toList) hpath
  simpa only [List.map_flatMap,List.flatMap_map,native_node_list] using hf

end RustCrypto.FullSign
