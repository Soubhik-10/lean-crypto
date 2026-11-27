module
public import Aeneas
public import EthLib.Cryptography.Sphincs.Serialization
@[expose] public section
namespace RustCrypto.CanonicalCorrectness
open EthLib.Cryptography.Sphincs
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

theorem read_list (bytes : ByteArray) (offset count : Nat) (hroom : offset+count ≤ bytes.size) :
    (EthLib.Base.readBytes bytes offset count hroom).toList = (bytes.data.toList.drop offset).take count := by
  apply List.ext_getElem
  · simp only [Vector.length_toList,List.length_take,List.length_drop,Array.length_toList]
    change count = min count (bytes.size-offset)
    omega
  · intro i hi hj
    rw [Vector.getElem_toList]
    simp only [EthLib.Base.readBytes,Vector.getElem_ofFn,List.getElem_take,List.getElem_drop,Array.getElem_toList]
    rfl

theorem read_field (bytes : ByteArray) (before suffix : List UInt8) {n : Nat} (field : Vector UInt8 n)
    (hbytes : bytes.data.toList = before ++ field.toList ++ suffix) :
    EthLib.Base.readBytes bytes before.length n (by
      have hb := congrArg List.length hbytes
      simp only [Array.length_toList,List.length_append,Vector.length_toList] at hb
      change before.length+n ≤ bytes.data.size
      omega) = field := by
  apply Vector.toList_inj.1
  rw [read_list,hbytes]
  simp

theorem counter_int_roundtrip (counter : UInt32) : toInt (toByte 4 counter.toNat) = counter.toNat := by
  have hb := counter.toNat_lt
  unfold toInt toByte
  rw [EthLib.Base.ByteOrder.ofBE_eq_foldl]
  simp only [EthLib.Base.ByteOrder.toBE,Vector.toList_mk,
    EthLib.Base.ByteOrder.toBE.go,List.foldl_cons,List.foldl_nil,UInt8.toNat_ofNat']
  norm_num1
  simp only [Nat.div_div_eq_div_mul] at *
  norm_num1 at *
  omega

theorem counter_roundtrip (counter : UInt32) : UInt32.ofNat (toInt (toByte 4 counter.toNat)) = counter := by
  rw [counter_int_roundtrip]
  exact UInt32.ofNat_toNat

/-- Splitting the flattening of a vector restores all its chunks. -/
theorem split_flatten {n m : Nat} (fields : Vector (Vector UInt8 m) n) : splitChunks fields.flatten = fields := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [splitChunks,Vector.getElem_ofFn,Vector.getElem_flatten]
  have he : (i*m+j)/m = i := by
    rw [Nat.add_comm,Nat.add_mul_div_right j i (by omega),Nat.div_eq_of_lt hj,Nat.zero_add]
  have hm : (i*m+j)%m = j := by simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  simp only [he,hm]

theorem tree_opening_ext (a b : TreeOpening) (hs : a.secret = b.secret) (hp : a.path = b.path) : a = b := by
  cases a
  cases b
  cases hs
  cases hp
  rfl

/-- Reading the encoded secret and ten path nodes restores one FORS opening. -/
theorem opening_roundtrip (opening : TreeOpening) : treeOpeningOfBytes (treeOpeningBytes opening) = opening := by
  apply tree_opening_ext
  · apply Vector.ext
    intro j hj
    simp only [treeOpeningOfBytes,treeOpeningBytes,Vector.getElem_ofFn,Vector.getElem_append]
    simp only [dite_eq_left hj]
  · have hp : (Vector.ofFn (fun j : Fin (Constants.FORS_HEIGHT*Constants.N) =>
        (treeOpeningBytes opening)[Constants.N+j.val]'(by have hj := j.isLt; change 16+j.val < 176; change j.val < 160 at hj; omega))) =
        opening.path.flatten := by
      apply Vector.ext
      intro j hj
      simp only [treeOpeningBytes,Vector.getElem_ofFn,Vector.getElem_append]
      simp only [show ¬Constants.N+j < Constants.N by omega,dite_false,Nat.add_sub_cancel_left]
    unfold treeOpeningOfBytes
    rw [hp]
    exact split_flatten opening.path

/-- Read a complete encoded FORS field from any surrounding byte strings. -/
theorem fors_field_roundtrip (bytes : ByteArray) (before after : List UInt8)
    (openings : Vector TreeOpening Constants.FORS_TREES)
    (hbytes : bytes.data.toList = before ++ (encodeFors openings).data.toList ++ after) :
    decodeFors bytes before.length (by
      have hb := congrArg List.length hbytes
      simp only [Array.length_toList,List.length_append,encodeFors,EthLib.Base.packBytes,
        Vector.size_toArray] at hb
      change before.length+Constants.FORS_TREES*Constants.TREE_OPENING_SIZE ≤ bytes.data.size
      omega) = openings := by
  unfold decodeFors
  have hr := read_field bytes before after ((openings.map treeOpeningBytes).flatten) hbytes
  rw [hr,split_flatten,Vector.map_map]
  simp only [Function.comp_def,opening_roundtrip]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]

theorem layer_encoded_list {layer : Layer} (sig : LayerSignature layer) :
    (encodeLayerSignature sig).data.toList = (toByte Constants.COUNTER_LEN sig.counter.toNat).toList ++
      sig.chainValues.flatten.toList ++ sig.path.flatten.toList := by
  simp only [encodeLayerSignature,packDigests,EthLib.Base.packBytes,ByteArray.data_append,Array.toList_append]
  rfl

theorem layer_encoded_length {layer : Layer} (sig : LayerSignature layer) :
    (encodeLayerSignature sig).data.toList.length = Constants.layerSigSize layer.height := by
  rw [layer_encoded_list]
  simp only [List.length_append,Vector.length_toList,Constants.layerSigSize]

/-- Reading an encoded layer restores its counter and every chain/path node. -/
theorem layer_field_roundtrip (bytes : ByteArray) (before after : List UInt8) {layer : Layer}
    (sig : LayerSignature layer)
    (hbytes : bytes.data.toList = before ++ (encodeLayerSignature sig).data.toList ++ after) :
    decodeLayerSignature layer bytes before.length (by
      have hb := congrArg List.length hbytes
      simp only [List.length_append] at hb
      rw [layer_encoded_length] at hb
      simp only [Array.length_toList] at hb
      change before.length+Constants.layerSigSize layer.height ≤ bytes.data.size
      omega) = sig := by
  have hc := read_field bytes before
    (sig.chainValues.flatten.toList ++ sig.path.flatten.toList ++ after)
    (toByte Constants.COUNTER_LEN sig.counter.toNat) (by
      simpa only [layer_encoded_list,List.append_assoc] using hbytes)
  have hv := read_field bytes (before ++ (toByte Constants.COUNTER_LEN sig.counter.toNat).toList)
    (sig.path.flatten.toList ++ after) sig.chainValues.flatten (by
      simpa only [layer_encoded_list,List.append_assoc] using hbytes)
  have hp := read_field bytes (before ++ (toByte Constants.COUNTER_LEN sig.counter.toNat).toList ++
    sig.chainValues.flatten.toList) after sig.path.flatten (by
      simpa only [layer_encoded_list,List.append_assoc] using hbytes)
  simp only [List.length_append,Vector.length_toList] at hv hp
  unfold decodeLayerSignature
  have hcr : UInt32.ofNat (toInt (toByte Constants.COUNTER_LEN sig.counter.toNat)) = sig.counter := counter_roundtrip sig.counter
  have hvr : splitDigests sig.chainValues.flatten = sig.chainValues := split_flatten sig.chainValues
  have hpr : splitDigests sig.path.flatten = sig.path := split_flatten sig.path
  rw [hc,hv,hp,hcr,hvr,hpr]

theorem fors_encoded_length (openings : Vector TreeOpening Constants.FORS_TREES) :
    (encodeFors openings).data.toList.length = 4224 := by
  simp only [encodeFors,EthLib.Base.packBytes,Array.length_toList,Vector.size_toArray]
  rfl

theorem signature_encoded_list (sig : Signature) :
    (encodeSignature sig).data.toList = sig.randomizer.toList ++ (encodeFors sig.fors).data.toList ++
      (encodeLayerSignature sig.bottom).data.toList ++ (encodeLayerSignature sig.middle).data.toList ++
      (encodeLayerSignature sig.top).data.toList := by
  simp only [encodeSignature,ByteArray.data_append,Array.toList_append,EthLib.Base.packBytes]
  rfl

theorem signature_encoded_length (sig : Signature) : (encodeSignature sig).size = Constants.SIG_SIZE := by
  have h := congrArg List.length (signature_encoded_list sig)
  simp only [Array.length_toList,List.length_append,Vector.length_toList] at h
  have hf := fors_encoded_length sig.fors
  have hb := layer_encoded_length sig.bottom
  have hm := layer_encoded_length sig.middle
  have ht := layer_encoded_length sig.top
  simp only [Array.length_toList] at hf hb hm ht
  change (encodeSignature sig).data.size = 7740
  rw [hf,hb,hm,ht] at h
  exact h

/-- Serialization is lossless for every typed signature, including arbitrary counters. -/
theorem signature_roundtrip (sig : Signature) : decodeSignature (encodeSignature sig) = .ok sig := by
  have hbytes := signature_encoded_list sig
  have hr := read_field (encodeSignature sig) []
    ((encodeFors sig.fors).data.toList ++ (encodeLayerSignature sig.bottom).data.toList ++
      (encodeLayerSignature sig.middle).data.toList ++ (encodeLayerSignature sig.top).data.toList)
    sig.randomizer (by simpa only [List.nil_append,List.append_assoc] using hbytes)
  have hf := fors_field_roundtrip (encodeSignature sig) sig.randomizer.toList
    ((encodeLayerSignature sig.bottom).data.toList ++ (encodeLayerSignature sig.middle).data.toList ++
      (encodeLayerSignature sig.top).data.toList) sig.fors (by simpa only [List.append_assoc] using hbytes)
  have hb := layer_field_roundtrip (encodeSignature sig)
    (sig.randomizer.toList ++ (encodeFors sig.fors).data.toList)
    ((encodeLayerSignature sig.middle).data.toList ++ (encodeLayerSignature sig.top).data.toList)
    sig.bottom (by simpa only [List.append_assoc] using hbytes)
  have hm := layer_field_roundtrip (encodeSignature sig)
    (sig.randomizer.toList ++ (encodeFors sig.fors).data.toList ++ (encodeLayerSignature sig.bottom).data.toList)
    (encodeLayerSignature sig.top).data.toList sig.middle (by simpa only [List.append_assoc] using hbytes)
  have ht := layer_field_roundtrip (encodeSignature sig)
    (sig.randomizer.toList ++ (encodeFors sig.fors).data.toList ++ (encodeLayerSignature sig.bottom).data.toList ++
      (encodeLayerSignature sig.middle).data.toList) [] sig.top (by simpa only [List.append_nil] using hbytes)
  simp only [List.length_nil] at hr
  simp only [List.length_append,Vector.length_toList,fors_encoded_length,layer_encoded_length] at hf hb hm ht
  have hf' : decodeFors (encodeSignature sig) forsOffset (by rw [signature_encoded_length]; decide) = sig.fors := hf
  have hb' : decodeLayerSignature .bottom (encodeSignature sig) bottomOffset (by rw [signature_encoded_length]; decide) = sig.bottom := hb
  have hm' : decodeLayerSignature .middle (encodeSignature sig) middleOffset (by rw [signature_encoded_length]; decide) = sig.middle := hm
  have ht' : decodeLayerSignature .top (encodeSignature sig) topOffset (by rw [signature_encoded_length]; decide) = sig.top := ht
  unfold decodeSignature
  rw [dite_eq_left (signature_encoded_length sig),hr,hf',hb',hm',ht']

end RustCrypto.CanonicalCorrectness
