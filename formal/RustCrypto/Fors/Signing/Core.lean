module
public import RustCrypto.Tree.Construction
public import RustCrypto.Fors.DigestBridge
public import RustCrypto.Serialization.Writer
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RustCrypto.ForsSigning
open RustCrypto.WotsChain RustCrypto.TweakableBridge RustCrypto.TreePrimitives RustCrypto.WotsEthlib
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def asBytes (values : List U8) : List UInt8 := values.map (fun b => UInt8.ofBitVec b.bv)

theorem path_bytes (nodes : Aeneas.Std.Array Node 10#usize)
    (path : Vector EthLib.Cryptography.Sphincs.Digest 10) (hpath : nodes.val.map nativeNode = path.toList) :
    asBytes (RustCrypto.Writer.headBytes nodes 10) = path.flatten.toList := by
  have ht : nodes.val.take 10 = nodes.val := List.take_of_length_le (by simp)
  have hf : path.flatten.toList = path.toList.flatMap Vector.toList := RustCrypto.OrderedVector.flatten_list path
  rw [hf]
  have h := congrArg (List.flatMap Vector.toList) hpath
  simpa only [asBytes,RustCrypto.Writer.headBytes,ht,List.map_flatMap,List.flatMap_map,native_node_list] using h

theorem section_write (input head tail : List U8) (hi : input.length = 176) (hh : head.length = 16) (ht : tail.length = 160) :
    (input.setSlice! 0 head).setSlice! 16 tail = head ++ tail := by
  rw [overwrite_layout_any input head 0 (by omega)]
  simp only [List.take_zero,List.nil_append,Nat.zero_add,hh]
  have hr : tail.length ≤ (input.drop 16).length := by simp only [List.length_drop,hi,ht]; omega
  have hp := RustCrypto.Writer.replace_after_prefix head (input.drop 16) tail hr
  rw [hh] at hp
  rw [hp]
  have hd : (input.drop 16).drop tail.length = [] := by
    rw [List.drop_drop,ht]
    exact List.drop_eq_nil_iff.mpr (by omega)
  rw [hd,List.append_nil]

@[irreducible] def opening (seed : Node) (secret : Aeneas.Std.Array U8 32#usize) (idx : Nat)
    (digest : Aeneas.Std.Array U8 34#usize) (kappa : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) :
    EthLib.Cryptography.Sphincs.TreeOpening × EthLib.Cryptography.Sphincs.Digest :=
  EthLib.Cryptography.Sphincs.treeOpen EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
    (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx kappa
    ((EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[kappa])

@[irreducible] def TreeResult (seed : Node) (idx : Nat)
    (reference : EthLib.Cryptography.Sphincs.TreeOpening × EthLib.Cryptography.Sphincs.Digest)
    (out : (Node × Node) × Address × Slice Node) : Prop :=
  nativeNode out.1.1 = reference.2 ∧ nativeNode out.1.2 = reference.1.secret ∧
  out.2.2.val.map nativeNode = reference.1.path.toList ∧
  TreePrimitives.frame out.2.1 seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree

theorem constructor_spec (address : Address) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (idx : Nat) (tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES) (selected : U32) (path : Slice Node)
    (hselected : selected.val < 1024) (hlen : path.val.length = 10)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.tree.build_tree address secret
      (.Fors (stepWord tree.val) (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf)) 10#u32 selected path
      ⦃ out => TreeResult seed idx
        (EthLib.Cryptography.Sphincs.treeOpen EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
          (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret))
          idx tree ⟨selected.val,hselected⟩) out ⦄ := by
  apply WP.spec_mono (BuildRoot.build_fors_opening_ethlib_spec address seed secret idx tree selected path hselected hlen hframe)
  intro out hout
  unfold TreeResult
  exact hout

@[step] theorem opening_bytes_spec : lean_sphincs.params.FORS_OPENING_BYTES ⦃ out => out.val = 176 ⦄ := by
  unfold lean_sphincs.params.FORS_OPENING_BYTES
  simp only [lean_sphincs.params.FORS_HEIGHT,lean_sphincs.params.NODE_BYTES]
  step*


@[step] theorem body_spec (address : Address) (seed : Node) (secret : Aeneas.Std.Array U8 32#usize)
    (digest : Aeneas.Std.Array U8 34#usize) (idx : Nat) (output : Slice U8) (roots : List U8) (kappa : Usize)
    (hkappa : kappa.val < 24) (hsize : 4224 ≤ output.val.length)
    (hframe : TreePrimitives.frame address seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree) :
    lean_sphincs.fors.sign_loop.body secret digest
      (stepWord (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).leaf) address output roots kappa ⦃ out =>
      match out with
      | .done _ => False
      | .cont (next,nextOutput,nextRoots,nextKappa) =>
          nextKappa.val = kappa.val+1 ∧
          TreePrimitives.frame next seed .bottom (EthLib.Cryptography.Sphincs.OtsKey.ofIndex .bottom idx).tree ∧
          asBytes nextOutput.val = (asBytes output.val).take (176*kappa.val) ++
            (EthLib.Cryptography.Sphincs.treeOpeningBytes (opening seed secret idx digest ⟨kappa.val,hkappa⟩).1).toList ++
            (asBytes output.val).drop (176*(kappa.val+1)) ∧
          asBytes nextRoots = asBytes roots ++ (opening seed secret idx digest ⟨kappa.val,hkappa⟩).2.toList ⦄ := by
  unfold lean_sphincs.fors.sign_loop.body
  simp only [lean_sphincs.params.FORS_TREES,lean_sphincs.params.FORS_HEIGHT,
    alloy_primitives.bits.fixed.FixedBytes.ZERO]
  have hrun : kappa < 24#usize := by scalar_tac
  rw [ite_eq_left hrun]
  iterate 19 step
  have hat : «at».val = kappa.val*10/8 := by scalar_tac
  have hi2 : i2.val = kappa.val*10/8+1 := by scalar_tac
  have hi4 : i4.val = kappa.val*10/8+2 := by scalar_tac
  have hmask : i12 = 1023#u32 := by scalar_tac
  have hshift : i9.val = 14-(kappa.val*10)%8 := by scalar_tac
  have h1 : i1 = digest.val[kappa.val*10/8]! := by
    rw [i1_post,← getElem!_pos digest.val «at».val (by scalar_tac),hat]
  have h3 : i3 = digest.val[kappa.val*10/8+1]! := by
    rw [i3_post,← getElem!_pos digest.val i2.val (by scalar_tac),hi2]
  have h5 : i5 = digest.val[kappa.val*10/8+2]! := by
    rw [i5_post,← getElem!_pos digest.val i4.val (by scalar_tac),hi4]
  have hmod (n : Nat) : n &&& 1023 = n % 1024 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod n 10
  have hselected : selected.val = RustCrypto.ForsDigest.selected digest kappa.val := by
    rw [selected_post,UScalar.val_and,hmask]
    have hv : (1023#u32).val = 1023 := rfl
    rw [hv,hmod,i10_post,field_post,hshift,h1,h3,h5]
    rfl
  have hselectedBound : selected.val < 1024 := by
    rw [hselected]
    exact Nat.mod_lt _ (by decide)
  have hcast : i13 = stepWord kappa.val := by
    have hv : i13.val = kappa.val := by scalar_tac
    apply UScalar.eq_of_val_eq
    change i13.val = kappa.val % 4294967296
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hv
  rw [hcast]
  have hslen : s.val.length = 10 := by rw [s_post]; simp
  let tree : Fin EthLib.Cryptography.Sphincs.Constants.FORS_TREES := ⟨kappa.val,hkappa⟩
  have hselectedCanonical : selected.val = EthLib.Cryptography.Sphincs.msbField
      (RustCrypto.ForsDigest.nativeDigest digest) (10*kappa.val) 10 :=
    hselected.trans (RustCrypto.ForsDigest.selected_ethlib digest kappa.val hkappa)
  have hfin : (⟨selected.val,hselectedBound⟩ : Fin (2^EthLib.Cryptography.Sphincs.Constants.FORS_HEIGHT)) =
      (EthLib.Cryptography.Sphincs.digestLeaves (RustCrypto.ForsDigest.nativeDigest digest))[tree] := by
    apply Fin.ext
    simp only [EthLib.Cryptography.Sphincs.digestLeaves,Fin.getElem_fin,Vector.getElem_ofFn]
    change selected.val = EthLib.Cryptography.Sphincs.msbField (RustCrypto.ForsDigest.nativeDigest digest) (10*kappa.val) 10
    exact hselectedCanonical
  have href : EthLib.Cryptography.Sphincs.treeOpen EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx tree
      ⟨selected.val,hselectedBound⟩ = ForsSigning.opening seed secret idx digest tree := by
    unfold ForsSigning.opening
    exact congrArg (fun leaf => EthLib.Cryptography.Sphincs.treeOpen EthLib.Cryptography.Sphincs.hashId (nativeNode seed)
      (EthLib.Cryptography.Sphincs.prf EthLib.Cryptography.Sphincs.hashId (nativeNode seed) (nativeSeed secret)) idx tree leaf) hfin
  have htree := constructor_spec address seed secret idx tree selected s hselectedBound hslen hframe
  rw [href] at htree
  step with htree as ⟨pair,next,nextPath,hconstructed⟩
  rcases pair with ⟨root,chosenSecret⟩
  unfold TreeResult at hconstructed
  rcases hconstructed with ⟨hroot,hsecret,hpath,hnext⟩
  dsimp only at hroot hsecret hpath hnext
  have hpathLen : nextPath.val.length = 10 := by
    calc
      _ = (nextPath.val.map nativeNode).length := by simp only [List.length_map]
      _ = (ForsSigning.opening seed secret idx digest tree).1.path.toList.length := congrArg List.length hpath
      _ = 10 := Vector.length_toList
  have harray : (to_slice_mut_back nextPath).val = nextPath.val := by
    rw [to_slice_mut_back_post]
    apply Aeneas.Std.Array.from_slice_val
    simpa using hpathLen
  have hpathBytes : asBytes (RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10) =
      (ForsSigning.opening seed secret idx digest tree).1.path.flatten.toList :=
    path_bytes (to_slice_mut_back nextPath) _ (by rw [harray]; exact hpath)
  simp only [Aeneas.Std.uncurry,alloy_primitives.utils.Keccak256.update,
    alloy_primitives.bits.fixed.FixedBytes.Insts.CoreConvertAsRefSliceU8.as_ref,
    alloy_primitives.bits.fixed.FixedBytes.as_slice,lean_sphincs.params.NODE_BYTES]
  iterate 5 step
  have hopen : opening.val.length = 176 := by scalar_tac
  step
  step by simpa [Aeneas.Std.Array.to_slice,Slice.length] using s2_post1
  have hhead : (index_mut_back1 s4).val = opening.val.setSlice! 0 chosenSecret.val := by
    rw [s2_post2,s4_post]
    simp only [Aeneas.Std.Array.to_slice,Slice.from_val]
  have hopenOne : (index_mut_back1 s4).length = 176 := by
    change (index_mut_back1 s4).val.length = 176
    rw [hhead,List.length_setSlice!,hopen]
  step
  step
  have hstart : i15.val = 176*kappa.val := by scalar_tac
  have hs5 : s5.val.length = 160 := by
    change s5.length = 160
    rw [s5_post1]
    change (index_mut_back1 s4).val.length - 16 = 160
    rw [hhead,List.length_setSlice!,hopen]
  have hcount : min 10 (s5.val.length/16) = 10 := by rw [hs5]; rfl
  have hs6 : s6.val = RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10 := by
    rw [s6_post,hcount]
    have hd : s5.val.drop 160 = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [Nat.reduceMul,hd,List.append_nil]
  have hnodeLen : chosenSecret.val.length = 16 := by simp
  have hnodesLen : (RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10).length = 160 := by
    exact RustCrypto.Writer.prefix_length (to_slice_mut_back nextPath) 10 (by simp)
  have hsection : (index_mut_back2 s6).val = chosenSecret.val ++ RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10 := by
    rw [s5_post2,hhead,hs6]
    exact section_write opening.val chosenSecret.val (RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10)
      hopen hnodeLen hnodesLen
  have hsecretBytes : asBytes chosenSecret.val = (ForsSigning.opening seed secret idx digest tree).1.secret.toList := by
    simpa only [native_node_list,asBytes] using congrArg Vector.toList hsecret
  have hencoded : asBytes (chosenSecret.val ++ RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10) =
      (EthLib.Cryptography.Sphincs.treeOpeningBytes (ForsSigning.opening seed secret idx digest tree).1).toList := by
    calc
      _ = asBytes chosenSecret.val ++ asBytes (RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10) := by
        simp only [asBytes,List.map_append]
      _ = _ := by rw [hsecretBytes,hpathBytes,EthLib.Cryptography.Sphincs.treeOpeningBytes,Vector.toList_append]
  refine ⟨i16_post,hnext,?_,?_⟩
  · rw [opening_post2]
    simp only [Slice.setSlice!,Slice.from_val]
    rw [hsection]
    have hmap : asBytes (output.val.setSlice! i15.val
        (chosenSecret.val ++ RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10)) =
        (asBytes output.val).setSlice! i15.val
          (asBytes (chosenSecret.val ++ RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10)) := by
      simp only [asBytes,List.map_setSlice!]
    rw [hmap]
    have hlenEncoded : (asBytes (chosenSecret.val ++ RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10)).length = 176 := by
      simp only [asBytes,List.length_map,List.length_append,hnodeLen,hnodesLen]
    rw [overwrite_layout_any (asBytes output.val)
      (asBytes (chosenSecret.val ++ RustCrypto.Writer.headBytes (to_slice_mut_back nextPath) 10)) i15.val (by
        simp only [asBytes,List.length_map] at hlenEncoded ⊢
        rw [hstart]
        omega),hlenEncoded,hstart,hencoded]
    have hend : 176*kappa.val+176 = 176*(kappa.val+1) := by omega
    rw [hend]
  · have hrootBytes : asBytes root.val = (ForsSigning.opening seed secret idx digest tree).2.toList := by
      simpa only [native_node_list,asBytes] using congrArg Vector.toList hroot
    have hcat : asBytes (roots ++ (Aeneas.Std.Array.to_slice root).val) = asBytes roots ++ asBytes root.val := by
      simp only [asBytes,List.map_append,Aeneas.Std.Array.to_slice,Slice.from_val]
    rw [hcat,hrootBytes]


end RustCrypto.ForsSigning
