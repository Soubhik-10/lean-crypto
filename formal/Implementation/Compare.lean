import Implementation.Algorithms
import Implementation.ReferenceCli

open HashSig HashSig.OverPermutation Sphincs
open SignatureKat (bitVecOf hexOf keccak Reader readFin take takeBigEndian)

/-! Diagnostic comparisons against the pinned statement, over actual Keccak-f[1600].
The byte readers, serialization, Keccak and compiled signer optimizations are upstream's.
This driver introduces no alternative Rust implementation or cryptographic assumptions. -/
namespace Implementation.Compare
open HashSig HashSig.OverPermutation Sphincs SignatureKat

def runCase (kind : String) (lines : List String) : Option String := do
  let raw (key : String) : Option (List UInt8) := (field lines key).bind hexBytes
  let nat (key : String) : Option Nat := (field lines key).bind String.toNat?
  match kind with
  | "indices" =>
    let index ← nat "index"
    if h : index < 2 ^ indexBits then
      let i : Index := ⟨index, h⟩
      return String.intercalate ";" ((List.finRange layerCount).map fun layer =>
        s!"{(leafOfIndex layer i).val},{(treeOfIndex layer i).val}")
    else none
  | "codeword" =>
    let code ← (← raw "code") |> bitVecOf 16
    let digits ← TargetSum.decodeDigest code
    return hexOf (List.ofFn fun i => UInt8.ofNat (digits i).val)
  | "digest" =>
    let pk ← (← raw "public_key") |> SignatureKat.Sphincs.publicKeyOf
    let message ← (← raw "message") |> bitVecOf 32
    let randomizer ← (← raw "randomizer") |> bitVecOf 16
    let digest := (Verification.messageDigest (m := StateM Unit) keccak pk randomizer message).run' ()
    return hexOf (littleEndianBytes 34 digest)
  | "wots" | "wots_sign" =>
    let pk ← (← raw "public_key") |> SignatureKat.Sphincs.publicKeyOf
    let l ← nat "layer"
    let t ← nat "tree"
    let e ← nat "leaf"
    let message ← (← raw "message") |> bitVecOf 16
    if hl : l < layerCount then
      if ht : t < 2 ^ indexBits then
        if he : e < 2 ^ layerHeight topLayer then
          let layer : Layer := ⟨l, hl⟩
          let tree : TreeIndex := ⟨t, ht⟩
          let leaf : TreeLeafIndex := ⟨e, he⟩
          if kind = "wots" then
            let bytes ← raw "signature"
            let ((counter, values), []) ← (do
              let c ← takeBigEndian 4
              let v ← readFin fun _ : ChainIndex => take 16
              return (c, v) : Reader _).run bytes | none
            let result := (Verification.otsLeaf (m := StateM Unit) keccak pk.publicSeed layer tree leaf
              message counter values).run' ()
            return hexOf (littleEndianBytes 16 (← result))
          else
            let seed ← (← raw "seed") |> bitVecOf 32
            let limit ← nat "limit"
            if limit > encodingAttemptLimit then none else do
              let key : KeyGenerationAndSigning.ExpandedKey := ⟨seed, 0, pk.publicSeed⟩
              let (counter, values) ← (KeyGenerationAndSigning.otsSignFrom (m := StateM Unit)
                keccak key layer tree leaf message limit 0).run' ()
              return hexOf (bigEndianBytes 4 counter ++ digestsPayload values)
        else none
      else none
    else none
  | "fors" =>
    let pk ← (← raw "public_key") |> SignatureKat.Sphincs.publicKeyOf
    let digest ← (← raw "digest") |> bitVecOf 34
    let bytes ← raw "opening"
    let (opening, []) ← (readFin fun _ : ForsTreeIndex => do
      let secret ← take 16
      let path ← readFin fun _ : Fin forsTreeHeight => take 16
      return (⟨secret, path⟩ : ForsTreeOpening)).run bytes | none
    let result := (Verification.forsRecover (m := StateM Unit) keccak pk.publicSeed
      (digestIndex digest) (digestForsLeaves digest) opening).run' ()
    return hexOf (littleEndianBytes 16 result)
  | "path" =>
    let pk ← (← raw "public_key") |> SignatureKat.Sphincs.publicKeyOf
    let height ← nat "height"
    let position ← nat "position"
    let value ← (← raw "node") |> bitVecOf 16
    let bytes ← raw "path"
    let (path, []) ← (readFin fun _ : Fin height => take 16).run bytes | none
    let result := (foldPath (m := StateM Unit) (fun level parent =>
      Verification.addressedHash keccak pk.publicSeed (makeAddress 2 0 .tree 0 (level + 1) parent))
      position (fun level => if h : level < height then path ⟨level, h⟩ else 0) height value).run' ()
    return hexOf (littleEndianBytes 16 result)
  | _ => none
end Implementation.Compare

def main (args : List String) : IO UInt32 := do
  let [directory] := args | do
    IO.eprintln "usage: implementation-kat CORPUS_DIR"
    return 2
  let mut mismatches : Nat := 0
  for kind in ["indices", "codeword", "digest", "wots", "wots_sign", "fors", "path"] do
    let directory := System.FilePath.mk directory / "components" / kind
    unless ← directory.isDir do
      IO.eprintln s!"missing component directory: {kind}"
      return 2
    let cases := ((← directory.readDir).map (·.path)).qsort (·.toString < ·.toString)
    for case in cases do
      let lines := (← IO.FS.readFile (case / "data.yaml")).splitOn "\n"
      let got := Implementation.Compare.runCase kind lines
      if got == SignatureKat.expected lines then
        IO.println s!"sphincs {kind} {case.fileName.getD ""}: ok"
      else
        IO.println s!"sphincs {kind} {case.fileName.getD ""}: MISMATCH expected {repr (SignatureKat.expected lines)}, got {repr got}"
        mismatches := mismatches + 1
  IO.println s!"{mismatches} mismatches"
  return if mismatches = 0 then 0 else 1