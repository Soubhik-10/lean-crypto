import LeanVM.Protocol.KnowledgeSoundness
import LeanVM.Prover.End
import LeanVM.Wire.OneEncoding
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Check the required end theorems, including all their transitive dependencies.
run_cmd do
  let env ← getEnv
  for name in #[`LeanVM.knowledgeSoundness_holds, `LeanVM.completeness_holds,
      `LeanVM.Wire.roundTrip, `LeanVM.Wire.oneEncoding] do
    let some info := env.find? name
      | throwError "missing required verifier theorem {name}"
    unless info.isTheorem do
      throwError "required declaration is not a theorem: {name}"
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "unexpected dependency {dependency} in {name}"
    logInfo m!"checked {name}: {dependencies}"
