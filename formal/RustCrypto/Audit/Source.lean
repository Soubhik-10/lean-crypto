module
import all LeanSphincs.Funs
import all RustCrypto.Keygen.Material
import all RustCrypto.Hash.ContextFrame
import all RustCrypto.Keygen.KeyGen
import all RustCrypto.Tree.Cache.Model
import all RustCrypto.Tree.Cache.Leaf
import all RustCrypto.Tree.Cache.LeafLoop
import all RustCrypto.Tree.Cache.ParentBody
import all RustCrypto.Tree.Cache.Update
import all RustCrypto.Tree.Cache.ParentLoop
import all RustCrypto.Tree.Cache.LevelsBody
import all RustCrypto.Tree.Cache.LevelsLoop
import all RustCrypto.Tree.Cache.New
import all RustCrypto.Tree.Cache.PathIndex
import all RustCrypto.Tree.Cache.Path
import all RustCrypto.Verification.Message.Bridge
import all RustCrypto.Verification.Message.Full
import all RustCrypto.Verification.Message.IndexBridge
import all RustCrypto.Verification.Message.IndexMachine
import all RustCrypto.Verification.Layer.Input
import all RustCrypto.Verification.Layer.Index
import all RustCrypto.Verification.Layer.Model
import all RustCrypto.Verification.Layer.Short
import all LeanSphincs.Types
import all LeanSphincs.TypesExternal
import all LeanSphincs.FunsExternal
import all RustCrypto.Common.Chunks
import all RustCrypto.Models.Simd
import all RustCrypto.Models.Compat
import all RustCrypto.Models.Parser
import all RustCrypto.Hash.Core
import all RustCrypto.Hash.Primitives
import all RustCrypto.Verification.Core
import all RustCrypto.Serialization.Writer
import all RustCrypto.Wots.Encoding.Codeword
import all RustCrypto.Wots.Encoding.CodewordBridge
import all RustCrypto.Wots.Chain
import all RustCrypto.Wots.Encoding.CounterSearch
import all RustCrypto.Common.ByteBridge
import all RustCrypto.Serialization.ReadBytes
import all RustCrypto.Serialization.WriteBytes
import all RustCrypto.Common.ByteRelations
import all RustCrypto.Signing.Bytes
import all RustCrypto.Tree.Climb
import all RustCrypto.Wots.Source
import all RustCrypto.Common.BigEndian
import all RustCrypto.Hash.AddressBridge
import all RustCrypto.Serialization.Parser
import all RustCrypto.Serialization.Index
import all RustCrypto.Hash.TweakableBridge
import all RustCrypto.Wots.ChainOrder
import all RustCrypto.Wots.Ethlib
import all RustCrypto.Hash.DomainFrame
import all RustCrypto.Wots.Prf
import all RustCrypto.Common.OrderedVector
import all RustCrypto.Common.VectorFlatten
import all RustCrypto.Wots.Public
import all RustCrypto.Wots.PublicLeafBridge
import all RustCrypto.Wots.Signing.Source
import all RustCrypto.Wots.Signing.Bridge
import all RustCrypto.Wots.Encoding.EncodingBridge
import all RustCrypto.Wots.Encoding.CounterBridge
import all RustCrypto.Wots.Encoding.SearchBridge
import all RustCrypto.Wots.Signing.Full
import all RustCrypto.Tree.ParentBridge
import all RustCrypto.Tree.Primitives
import all RustCrypto.Fors.Positions
import all RustCrypto.Fors.Primitives
import all RustCrypto.Tree.ClimbBridge
import all RustCrypto.Fors.Climb
import all RustCrypto.Fors.Window
import all RustCrypto.Fors.Digest
import all RustCrypto.Fors.DigestBridge
import all RustCrypto.Tree.Build.Finish
import all RustCrypto.Tree.Build.Root
import all RustCrypto.Tree.Build.RootBridge
import all RustCrypto.Tree.Build.Selection
import all RustCrypto.Tree.Build.Secret
import all RustCrypto.Tree.Build.SecretBridge
import all RustCrypto.Tree.Build.FinishPath
import all RustCrypto.Tree.Build.Coverage
import all RustCrypto.Tree.Build.PathPatch
import all RustCrypto.Tree.Build.Path
import all RustCrypto.Tree.Build.RootCoverage
import all RustCrypto.Tree.MerklePath
import all RustCrypto.Tree.MerkleBuilt
import all RustCrypto.Tree.Build.Models
import all RustCrypto.Tree.Build.ConstructorPath
import all RustCrypto.Tree.Construction
import all RustCrypto.Common.OrderedPrefix
import all RustCrypto.Fors.Signing.Core
import all RustCrypto.Fors.Signing.Loop
import all RustCrypto.Fors.Signing.Full
import all RustCrypto.Fors.Scalar.Bytes
import all RustCrypto.Fors.Scalar.Layout
import all RustCrypto.Tree.ClimbShort
import all RustCrypto.Wots.Recovery.Model
import all RustCrypto.Wots.Recovery.Layout
import all RustCrypto.Wots.Recovery.Canonical
import all RustCrypto.Wots.Encoding.CounterBytes
import all RustCrypto.Wots.Encoding.Read
import all RustCrypto.Wots.Backend
import all RustCrypto.Wots.Entry
import all RustCrypto.Serialization.Layout.Read
import all RustCrypto.Serialization.Layout.Node
import all RustCrypto.Serialization.Layout.Counter
import all RustCrypto.Serialization.Layout.Digests
import all RustCrypto.Serialization.Layout.Layer
import all RustCrypto.Serialization.Layout.Opening
import all RustCrypto.Serialization.Layout.Fors
import all RustCrypto.Serialization.Layout.Signature
import all RustCrypto.Formatting.Numeric
import all RustCrypto.Formatting.Laws
import all RustCrypto.Formatting.Template
import all RustCrypto.Formatting.Source
import all RustCrypto.Formatting.Output
import all RustCrypto.Correctness.Merkle
import all RustCrypto.Correctness.Trees
import all RustCrypto.Verification.Model
import all RustCrypto.Verification.Index
import all RustCrypto.Verification.Compare
import all RustCrypto.Verification.Api
import all RustCrypto.Verification.Decoded
import all RustCrypto.Verification.Root.Model
import all RustCrypto.Signing.Full.Wots
import all RustCrypto.Signing.Full.Path
import all RustCrypto.Signing.Full.Constants
import all RustCrypto.Signing.Full.Model
import all RustCrypto.Signing.Full.Buffer
import all RustCrypto.Signing.Full.Failure
import all RustCrypto.Signing.Full.SelectPath
import all RustCrypto.Signing.Full.Success
import all RustCrypto.Signing.Full.Loop
import all RustCrypto.Signing.Full.Native
import all RustCrypto.Signing.Full.Index
import all RustCrypto.Signing.Full.Public
import all RustCrypto.Signing.Full.Core
import all RustCrypto.Correctness.Wots
import all RustCrypto.Correctness.PublicKey
import all RustCrypto.Correctness.Signing.Serialization
import all RustCrypto.Correctness.Signing.Core
import all RustCrypto.Correctness.Signing.Success
import all RustCrypto.Correctness.Signing.Api
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
