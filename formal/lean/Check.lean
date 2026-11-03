import Lean
import DevEnv

/-! Audit every declaration originating in our modules, including private
helpers, definitions and unused axioms. A new module only needs to be imported
by DevEnv.lean; there is no theorem allowlist to keep in sync. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless (`DevEnv).isPrefixOf moduleName do continue
    count := count + 1
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on forbidden axiom {axiomName}"
  if count == 0 then throwError "No DevEnv declarations were audited"
  logInfo m!"Axiom audit passed for {count} declarations (only propext, Classical.choice, Quot.sound allowed)"
