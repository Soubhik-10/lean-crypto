import Implementation.Algorithms
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Require the documented public theorems individually: generated helper lemmas
-- cannot stand in for a missing proof. Kernel checking remains enabled separately.
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    `Implementation.indexBefore_eq,
    `Implementation.layer_indices,
    `Implementation.scheduledEnds_eq_walkChain,
    `Implementation.scheduledEnds_eq_recoverChain,
    `Implementation.search_none_iff,
    `Implementation.search_some_spec,
    `Implementation.search_counter_no_wrap,
    `Implementation.search_eq_otsSignFrom]
  for name in required do
    let some info := env.find? name
      | throwError "missing required implementation theorem {name}"
    unless info.isTheorem do
      throwError "required implementation declaration is not a theorem: {name}"
  -- Keep checking every theorem, including all generated helpers and future additions.
  for (name, info) in env.constants.toList do
    if (`Implementation).isPrefixOf name && info.isTheorem then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "unexpected dependency {dependency} in {name}"
      logInfo m!"checked {name}: {dependencies}"
