import QFixLean
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Audit the transitive axiom dependencies of declarations from imported QFixLean
modules. Select declarations by their defining module, not their namespace, so
declarations placed in other namespaces are checked too. Imported helper
lemmas and private proof dependencies are included by `Lean.collectAxioms`.

Run after `lake build --wfail`:
  lake env lean -DwarningAsError=true scripts/CheckAxioms.lean

This checks proof dependencies, not whether theorem statements express the
intended mathematical specification. The public import-list check in CI
ensures that all project modules are imported by QFixLean.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`QFixLean).isPrefixOf env.header.moduleNames[idx]! do
      continue
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    for ax in axioms do
      unless seen.contains ax do
        seen := seen.push ax
    count := count + 1
  unless count > 0 do
    throwError "No QFixLean declarations found; check the library imports"
  logInfo m!"Axiom audit passed for {count} declarations from QFixLean modules. \
    Axiom union: {seen.qsort Name.lt}"
