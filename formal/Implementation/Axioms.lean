import Implementation.Algorithms
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Check every new theorem, including generated helper theorems, rather than a short list
-- that could silently omit a later proof. Kernel checking remains enabled separately.
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Implementation).isPrefixOf name && info.isTheorem then
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "unexpected dependency {dependency} in {name}"
      logInfo m!"checked {name}: {dependencies}"
      checked := checked + 1
  unless checked ≥ 8 do
    throwError "implementation proof inventory is incomplete: {checked}"