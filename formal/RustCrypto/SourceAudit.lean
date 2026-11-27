module
import all LeanSphincs.Funs
import all RustCrypto.KeyMaterial
import all RustCrypto.ContextFrame
import all RustCrypto.KeyGen
import all RustCrypto.TopCacheModel
import all RustCrypto.TopCacheLeaf
import all RustCrypto.TopCacheLeafLoop
import all RustCrypto.TopCacheParentBody
import all RustCrypto.TopCacheUpdate
import all RustCrypto.TopCacheParentLoop
import all RustCrypto.TopCacheLevelsBody
import all RustCrypto.TopCacheLevelsLoop
import all RustCrypto.TopCacheNew
import all RustCrypto.TopCachePathIndex
import all RustCrypto.TopCachePath
import all RustCrypto.MessageHashBridge
import all RustCrypto.MessageHashFull
import all RustCrypto.DigestIndexBridge
import all RustCrypto.DigestIndexMachine
import all RustCrypto.LayerInput
import all RustCrypto.LayerIndex
import all RustCrypto.RecoverLayer
import all RustCrypto.RecoverLayerShort
import all LeanSphincs.Types
import all LeanSphincs.TypesExternal
import all LeanSphincs.FunsExternal
import all RustCrypto.Chunks
import all RustCrypto.Simd
import all RustCrypto.Compat
import all RustParser.Models
import all RustCrypto.Hash
import all RustCrypto.HashPrimitives
import all RustCrypto.Verifier
import all RustCrypto.Writer
import all RustCrypto.Codeword
import all RustCrypto.CodewordBridge
import all RustCrypto.WotsChain
import all RustCrypto.CounterSearch
import all RustCrypto.ByteBridge
import all RustCrypto.ReadBytes
import all RustCrypto.WriteBytes
import all RustCrypto.ByteRelations
import all RustCrypto.SigningBytes
import all RustCrypto.Climb
import all RustCrypto.WotsSource
import all RustCrypto.BigEndian
import all RustCrypto.AddressBridge
import all RustParser
import all RustIndex
import all RustCrypto.TweakableBridge
import all RustCrypto.ChainOrder
import all RustCrypto.WotsEthlib
import all RustCrypto.DomainFrame
import all RustCrypto.WotsPrf
import all RustCrypto.OrderedVector
import all RustCrypto.VectorFlatten
import all RustCrypto.WotsPublic
import all RustCrypto.PublicLeafBridge
import all RustCrypto.WotsSignSource
import all RustCrypto.WotsSignBridge
import all RustCrypto.EncodingBridge
import all RustCrypto.CounterBridge
import all RustCrypto.SearchBridge
import all RustCrypto.WotsSignFull
import all RustCrypto.ParentBridge
import all RustCrypto.TreePrimitives
import all RustCrypto.ForsPositions
import all RustCrypto.ForsPrimitives
import all RustCrypto.ClimbBridge
import all RustCrypto.ForsClimb
import all RustCrypto.ForsWindow
import all RustCrypto.ForsDigest
import all RustCrypto.ForsDigestBridge
import all RustCrypto.BuildFinish
import all RustCrypto.BuildRoot
import all RustCrypto.RootBridge
import all RustCrypto.Selection
import all RustCrypto.BuildSecret
import all RustCrypto.SecretBridge
import all RustCrypto.FinishPath
import all RustCrypto.Coverage
import all RustCrypto.PathPatch
import all RustCrypto.BuildPath
import all RustCrypto.RootCoverage
import all RustCrypto.MerklePath
import all RustCrypto.MerkleBuilt
import all RustCrypto.ConstructionModels
import all RustCrypto.ConstructorPath
import all RustCrypto.TreeConstruction
import all RustCrypto.OrderedPrefix
import all RustCrypto.ForsSigning
import all RustCrypto.ForsSigningLoop
import all RustCrypto.ForsSigningFull
import all RustCrypto.ForsScalarBytes
import all RustCrypto.ForsScalarLayout
import all RustCrypto.ClimbShort
import all RustCrypto.WotsRecoverModel
import all RustCrypto.WotsRecoverLayout
import all RustCrypto.WotsRecoverCanonical
import all RustCrypto.WotsCounterBytes
import all RustCrypto.WotsEncodingRead
import all RustCrypto.WotsBackend
import all RustCrypto.WotsEntry
import all RustCrypto.LayoutRead
import all RustCrypto.LayoutNode
import all RustCrypto.LayoutCounter
import all RustCrypto.LayoutDigests
import all RustCrypto.LayoutLayer
import all RustCrypto.LayoutOpening
import all RustCrypto.LayoutFors
import all RustCrypto.LayoutSignature
import all RustCrypto.FmtNumeric
import all RustCrypto.FmtLaws
import all RustCrypto.FmtTemplate
import all RustCrypto.FmtSource
import all RustCrypto.FmtOutput
import all RustCrypto.CanonicalMerkle
import all RustCrypto.CanonicalTrees
import all RustCrypto.WholeVerifyModel
import all RustCrypto.WholeVerifyIndex
import all RustCrypto.WholeVerifyCompare
import all RustCrypto.WholeVerifyApi
import all RustCrypto.WholeVerifyDecoded
import all RustCrypto.WholeRoot
import all RustCrypto.FullSignWots
import all RustCrypto.FullSignPath
import all RustCrypto.FullSignConstants
import all RustCrypto.FullSignModel
import all RustCrypto.FullSignBuffer
import all RustCrypto.FullSignFailure
import all RustCrypto.FullSignSelectPath
import all RustCrypto.FullSignSuccess
import all RustCrypto.FullSignLoop
import all RustCrypto.FullSignNative
import all RustCrypto.FullSignIndex
import all RustCrypto.FullSignPublic
import all RustCrypto.FullSign
import all RustCrypto.CanonicalWots
import all RustCrypto.CanonicalPublicKey
import all RustCrypto.CanonicalSigningSerialization
import all RustCrypto.CanonicalSigning
import all RustCrypto.CanonicalSigningSuccess
import all RustCrypto.CanonicalSigningApi
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let required : List Name := [
    `RustCrypto.FullSign.sign_with_limit_ethlib_spec,
    `RustCrypto.FullSign.sign_ethlib_spec,
    `RustCrypto.FullSign.layer_signature_bytes,
    `RustCrypto.FullSign.loop_spec,
    `RustCrypto.CanonicalCorrectness.public_key_decode_encode,
    `RustCrypto.CanonicalCorrectness.signature_roundtrip,
    `RustCrypto.CanonicalCorrectness.native_sign_success,
    `RustCrypto.CanonicalCorrectness.otsLeaf_findCounter,
    `RustCrypto.CanonicalCorrectness.sign_with_limit_roundtrip_with_contract,
    `RustCrypto.CanonicalCorrectness.sign_roundtrip_with_contract,

    `RustCrypto.CanonicalCorrectness.climb_path,
    `RustCrypto.CanonicalCorrectness.xmss_fold_path,
    `RustCrypto.CanonicalCorrectness.tree_recover_open,
    `RustCrypto.CanonicalCorrectness.fors_recover_sign,
    `RustCrypto.WholeVerifier.recover_root_with_backends,
    `RustCrypto.WholeVerifier.verify_decoded_with_recovery,
    `RustCrypto.WholeVerifier.expected_verify_decoded,
    `RustCrypto.ErrorFormatting.source_display_program,
    `RustCrypto.ErrorFormatting.source_debug_program,
    `RustCrypto.ErrorFormatting.source_clone,
    `RustCrypto.ErrorFormatting.source_equality,
    `RustCrypto.ErrorFormatting.source_equality_iff,
    `RustCrypto.ErrorFormatting.source_eq_assertion,
    `RustCrypto.ErrorFormatting.source_error_debug,
    `RustCrypto.ErrorFormatting.source_error_display,
    `RustCrypto.ErrorFormatting.display_output,
    `RustCrypto.ErrorFormatting.debug_output,
    `RustCrypto.ErrorFormatting.debug_pretty_output,
    `RustCrypto.ErrorFormatting.display_partial_writer_failure,
    `RustCrypto.ErrorFormatting.debug_partial_writer_failure,
    `RustCrypto.ErrorFormatting.source_display_prefix_error,

    `RustCrypto.Layout.public_key_decode,
    `RustCrypto.Layout.signature_decode,
    `RustCrypto.Layout.signature_decode_total,
    `RustCrypto.Layout.fors_decode,
    `RustCrypto.Layout.layer_signature_decode,
    `RustCrypto.LayerInput.take_layer_typed_spec,
    `RustCrypto.LayerInput.recover_layer_with_backend,
    `RustCrypto.LayerInput.recover_layer_short_with_backend,
    `RustCrypto.LayerInput.recover_layer_total_with_backend,
    `RustCrypto.MessageHashBridge.native_digest_list,
    `RustCrypto.MessageHashBridge.randomizer_ethlib_spec,
    `RustCrypto.MessageHashBridge.hmsg_list,
    `RustCrypto.MessageHashBridge.message_digest_bytes_ethlib_spec,
    `RustCrypto.MessageHashBridge.digest_index_native,
    `RustCrypto.MessageHashBridge.masked_tree_val,
    `RustCrypto.MessageHashBridge.merge_index_spec,

    `RustCrypto.TopCache.new_ethlib_spec,
    `RustCrypto.TopCache.root_ethlib_spec,
    `RustCrypto.TopCache.path_ethlib_spec,
    `RustCrypto.TopCache.leaf_loop_spec,
    `RustCrypto.TopCache.parent_loop_spec,
    `RustCrypto.TopCache.levels_loop_spec,
    `RustCrypto.TopCache.heap_path_index,

    `RustCrypto.ContextFrame.context_frame_spec,
    `RustCrypto.ContextFrame.set_tree_frame_spec,
    `RustCrypto.KeyGen.max_tree_height_spec,
    `RustCrypto.KeyGen.key_gen_ethlib_spec,
    `RustCrypto.KeyMaterial.expand_key_ethlib_spec,
    `RustCrypto.WotsRecover.counter_bytes_roundtrip,
    `RustCrypto.WotsRecover.encode_counter_spec,
    `RustCrypto.WotsRecover.codeword_native_spec,
    `RustCrypto.WotsRecover.entry_with_backend,
    `RustCrypto.WotsRecover.walk_end_spec,
    `RustCrypto.WotsRecover.digit_relation_of_values,
    `RustCrypto.WotsRecover.ends_reference,
    `RustCrypto.WotsRecover.canonical_leaf,
    `RustCrypto.WotsRecover.ends_full,
    `RustCrypto.ForsRead.nodeAt_val,
    `RustCrypto.ForsRead.serialized_nodes,
    `RustCrypto.ForsRead.decodedOpening_drop,
    `RustCrypto.ClimbBridge.recover_key_failure,
    `RustCrypto.ClimbBridge.climb_key_short_spec,
    `RustCrypto.ForsSigning.constructor_spec,
    `RustCrypto.ForsSigning.body_spec,
    `RustCrypto.ForsSigning.loop_spec,
    `RustCrypto.ForsSigning.canonical_sign,
    `RustCrypto.ForsSigning.encoded_full,
    `RustCrypto.ForsSigning.roots_full,
    `RustCrypto.ForsSigning.sign_ethlib_spec,
    `RustCrypto.OrderedPrefix.replace_next,
    `RustCrypto.MerklePath.build_value,
    `RustCrypto.MerklePath.build_path_list,
    `RustCrypto.BuildRoot.build_tree_path_ethlib_spec,
    `RustCrypto.BuildRoot.build_fors_opening_ethlib_spec,
    `RustCrypto.BuildRoot.build_xmss_opening_ethlib_spec,
    `RustCrypto.ForsDigest.window_field_eq,
    `RustCrypto.ForsDigest.leaf_position_spec,
    `RustCrypto.ForsDigest.leaf_position_ethlib_spec,
    `RustCrypto.BuildRoot.finish_spec,
    `RustCrypto.BuildRoot.build_subtree_root_spec,
    `RustCrypto.BuildRoot.build_fors_root_ethlib_spec,
    `RustCrypto.BuildRoot.build_xmss_root_ethlib_spec,
    `RustCrypto.BuildRoot.build_subtree_secret_spec,
    `RustCrypto.BuildRoot.build_fors_secret_ethlib_spec,
    `RustCrypto.BuildRoot.finish_path_spec,
    `RustCrypto.BuildRoot.build_subtree_path_spec,
    `RustCrypto.BuildRoot.patch_full_path,
    `RustCrypto.MerklePath.siblings_list,
    `RustCrypto.TreePrimitives.xmss_leaf_spec,
    `RustCrypto.TreePrimitives.xmss_parent_spec,
    `RustCrypto.ForsPositions.position_shift_spec,
    `RustCrypto.ForsPrimitives.fors_leaf_spec,
    `RustCrypto.ForsPrimitives.fors_parent_spec,
    `RustCrypto.ClimbBridge.climb_key_ethlib_spec,
    `RustCrypto.ClimbBridge.climb_xmss_ethlib_spec,
    `RustCrypto.ForsClimb.climb_fors_ethlib_spec,
    `RustParser.is_empty_eq,
    `RustParser.new_eq,
    `RustParser.take_success,
    `RustParser.take_failure,
    `RustParser.take_total,
    `RustParser.successful_read_conserves_bytes,
    `RustParser.successful_read_length,
    `RustParser.take_zero,
    `RustIndex.take_layer8_spec,
    `RustIndex.take_layer10_spec,
    `RustIndex.layer_heights_eq,
    `RustIndex.take_layer_production_spec,
    `RustCrypto.context_new_spec,
    `RustCrypto.set_tree_spec,
    `RustCrypto.set_domain_spec,
    `RustCrypto.set_position_spec,
    `RustCrypto.accumulator_spec,
    `RustCrypto.truncate_spec,
    `RustCrypto.node_input_spec,
    `RustCrypto.parent_input_spec,
    `RustCrypto.derive_secret_spec,
    `RustCrypto.hash_node_spec,
    `RustCrypto.hash_parent_spec,
    `RustCrypto.encode_spec,
    `RustCrypto.message_digest_spec,
    `RustCrypto.Writer.write_nodes_spec,
    `RustCrypto.Verifier.wrong_length_rejected,
    `RustCrypto.Verifier.truncated_randomizer_rejected,
    `RustCrypto.Verifier.failed_recovery_rejected,
    `RustCrypto.Codeword.codeword_spec,
    `RustCrypto.Codeword.codeword_ethlib_spec,
    `RustCrypto.WotsChain.walk_chain_spec,
    `RustCrypto.CounterSearch.find_encoding_spec,
    `RustCrypto.ByteBridge.decode_eight,
    `RustCrypto.ByteBridge.encode_eight,
    `RustCrypto.ByteBridge.digest_native,
    `RustCrypto.ByteBridge.encode32,
    `RustCrypto.ByteBridge.encode64,
    `RustCrypto.ByteBridge.tree96,
    `RustCrypto.SigningBytes.expand_key_spec,
    `RustCrypto.SigningBytes.randomizer_spec,
    `RustCrypto.Climb.climb_spec,
    `RustCrypto.WotsSource.chain_start_spec,
    `RustCrypto.WotsSource.public_leaf_spec,
    `RustCrypto.AddressBridge.canonical_prefix,
    `RustCrypto.TweakableBridge.hash_node_ethlib_spec,
    `RustCrypto.WotsSignSource.sign_spec,
    `RustCrypto.WotsEthlib.derive_secret_ethlib_spec,
    `RustCrypto.WotsEthlib.walk_chain_ethlib_spec,
    `RustCrypto.WotsEthlib.chain_start_ethlib_spec,
    `RustCrypto.WotsEthlib.public_leaf_ethlib_spec,
    `RustCrypto.WotsEthlib.find_encoding_ethlib_spec,
    `RustCrypto.WotsEthlib.sign_ethlib_spec,
    `RustCrypto.WotsEthlib.sign_any_pair_ethlib_spec,
    `RustCrypto.WotsEthlib.public_leaf_any_pair_ethlib_spec,
    `RustCrypto.TweakableBridge.hash_parent_ethlib_spec]
  let simdRequired : List Name := if env.contains `lean_sphincs.hash.batch.hash then [
    `RustCrypto.Layout.simd_canonical_recover_scalar,
    `RustCrypto.ForsForest.body_short_spec,
    `RustCrypto.ForsForest.short_loop_spec,
    `RustCrypto.ForsForest.recover_trees_short_spec,
    `RustCrypto.ForsForest.recover_fors_short_spec,
    `RustCrypto.ForsForest.recover_fors_total_spec,
    `RustCrypto.ForsForest.clone_spec,
    `RustCrypto.ForsForest.position_array_spec,
    `RustCrypto.ForsForest.first_batch_spec,
    `RustCrypto.ForsForest.openingAt_val,
    `RustCrypto.ForsForest.native_group,
    `RustCrypto.ForsForest.forest_body_spec,
    `RustCrypto.ForsForest.forest_loop_spec,
    `RustCrypto.ForsForest.recover_trees_spec,
    `RustCrypto.ForsForest.canonical_recover,
    `RustCrypto.ForsForest.recover_fors_ethlib_spec,
    `RustCrypto.ForsBatch.chunk_at,
    `RustCrypto.ForsBatch.sibling_array_spec,
    `RustCrypto.ForsBatch.first_array_spec,
    `RustCrypto.ForsBatch.parent_array_spec,
    `RustCrypto.ForsBatch.batch_body_spec,
    `RustCrypto.ForsBatch.batch_loop_spec,
    `RustCrypto.ForsBatch.recover_batch_spec,
    `RustCrypto.ForsBatch.walk_native,
    `RustCrypto.ForsBatch.opening_secret,
    `RustCrypto.ForsBatch.opening_path,
    `RustCrypto.ForsBatch.leaf_step_native,
    `RustCrypto.ForsBatch.recover_batch_ethlib_spec,
    `RustCrypto.AppendNodes.append_nodes_spec,
    `RustCrypto.SimdRound.rotate_spec,
    `RustCrypto.Constants.rotation_table_spec,
    `RustCrypto.RoundConstants.round_table_exact_spec,
    `RustCrypto.Permutation.chi_array_spec,
    `RustCrypto.Permutation.permute_ethlib_spec,
    `RustCrypto.ShortHash.hash_64_spec,
    `RustCrypto.ShortHash.hash_80_spec,
    `RustCrypto.ShortHash.hash_64_bytes_spec,
    `RustCrypto.ShortHash.hash_80_bytes_spec,
    `RustCrypto.BatchNodes.hash_nodes_spec,
    `RustCrypto.BatchParents.hash_parents_spec,
    `RustCrypto.BatchPositions.set_positions_spec] else []
  let scalarRequired : List Name := if env.contains `lean_sphincs.hash.batch.hash then [] else [
    `RustCrypto.ForsScalar.body_short_spec,
    `RustCrypto.ForsScalar.short_loop_spec,
    `RustCrypto.ForsScalar.recover_trees_short_spec,
    `RustCrypto.ForsScalar.recover_fors_short_spec,
    `RustCrypto.ForsScalar.recover_fors_total_spec,
    `RustCrypto.ForsScalar.body_spec,
    `RustCrypto.ForsScalar.loop_spec,
    `RustCrypto.ForsScalar.recover_trees_spec,
    `RustCrypto.ForsScalar.canonical_recover,
    `RustCrypto.ForsScalar.recover_fors_ethlib_spec]
  let wotsScalarRequired : List Name := if env.contains `lean_sphincs.wots.recover_window then [] else [
    `RustCrypto.WotsRecover.scalar_backend_contract,
    `RustCrypto.WotsRecover.recover_wots_scalar_ethlib_spec,
    `RustCrypto.WotsRecover.scalar_body_spec,
    `RustCrypto.WotsRecover.scalar_loop_spec,
    `RustCrypto.WotsRecover.scalar_body_short_spec,
    `RustCrypto.WotsRecover.scalar_short_loop_spec,
    `RustCrypto.WotsRecover.scalar_chains_total_spec]
  let wotsAvx2Required : List Name := if env.contains `lean_sphincs.wots.recover_window then [
    `RustCrypto.WotsAvx2.read_window_total_spec,
    `RustCrypto.WotsAvx2.scatter_four_native,
    `RustCrypto.WotsAvx2.progress_end,
    `RustCrypto.WotsAvx2.recover_group_spec,
    `RustCrypto.WotsAvx2.scan_loop_spec,
    `RustCrypto.WotsAvx2.tail_loop_spec,
    `RustCrypto.WotsAvx2.round_body_spec,
    `RustCrypto.WotsAvx2.recover_window_ethlib_spec,
    `RustCrypto.WotsAvx2.chains_loop_spec,
    `RustCrypto.WotsAvx2.chains_short_loop_spec,
    `RustCrypto.WotsAvx2.avx2_chains_total_spec,
    `RustCrypto.WotsRecover.avx2_backend_contract,
    `RustCrypto.WotsRecover.recover_wots_avx2_ethlib_spec] else []
  let recoverLayerRequired : List Name := if env.contains `lean_sphincs.wots.recover_window then [
    `RustCrypto.LayerInput.recover_layer_avx2_ethlib_spec] else [
    `RustCrypto.LayerInput.recover_layer_scalar_ethlib_spec]
  let wholeVerifierRequired : List Name := if env.contains `lean_sphincs.wots.recover_window then [
    `RustCrypto.WholeVerifier.recover_root_avx2_contract,
    `RustCrypto.WholeVerifier.verify_avx2_ethlib_spec] else if env.contains `lean_sphincs.hash.batch.hash then [
    `RustCrypto.WholeVerifier.recover_root_sse2_contract,
    `RustCrypto.WholeVerifier.verify_sse2_ethlib_spec] else [
    `RustCrypto.WholeVerifier.recover_root_scalar_contract,
    `RustCrypto.WholeVerifier.verify_scalar_ethlib_spec]
  let signingRequired : List Name := if env.contains `lean_sphincs.wots.recover_window then [
    `RustCrypto.CanonicalCorrectness.sign_with_limit_roundtrip_avx2,
    `RustCrypto.CanonicalCorrectness.sign_roundtrip_avx2] else if env.contains `lean_sphincs.hash.batch.hash then [
    `RustCrypto.CanonicalCorrectness.sign_with_limit_roundtrip_sse2,
    `RustCrypto.CanonicalCorrectness.sign_roundtrip_sse2] else [
    `RustCrypto.CanonicalCorrectness.sign_with_limit_roundtrip_scalar,
    `RustCrypto.CanonicalCorrectness.sign_roundtrip_scalar]
  for requiredName in (required ++ simdRequired ++ scalarRequired ++ wotsScalarRequired ++ wotsAvx2Required ++ recoverLayerRequired ++ wholeVerifierRequired ++ signingRequired) do
    match env.find? requiredName with
    | some (.thmInfo _) => pure ()
    | _ => throwError "required correctness theorem missing: {requiredName}"
  let mut count : Nat := 0
  for (declName, info) in env.constants.toList do
    if [`lean_sphincs, `RustCrypto, `RustParser, `RustIndex].any (·.isPrefixOf declName) then
      if info.isAxiom then throwError "unexpected dependency {declName}: declared assumption"
      else
        let dependencies ← collectAxioms declName
        dependencies.forM fun dependency => do
          unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
            throwError "unexpected dependency {dependency} in {declName}"
        count := count + 1
  logInfo m!"audited {count} source-derived declarations"
