import Lean

/-! Failing transitive axiom audits for checked verification. Audit definitions
as well as theorems: translation/admission certificates and VerifiedArtifact
packages are data containing proofs. This module implements the checked policy
only; a future explicit solver-trust policy must use a distinct interface. -/

namespace VeriPyAsm.Verification.AxiomAudit

open Lean

def approved : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Inspect the complete kernel dependency closure, including declaration types.
Unknown or unchecked declarations fail rather than having an empty audit. -/
def checkDeclaration (name : Name) : CoreM Unit := do
  let environment ← getEnv
  let some info := environment.checked.get.find? name
    | throwError "axiom audit: no kernel-checked declaration {name}"
  if info.isUnsafe || info.isPartial then
    throwError "axiom audit: {name} is not a safe kernel declaration"
  let unexpected := (← collectAxioms name).filter (fun axiomName => !approved.contains axiomName)
  unless unexpected.isEmpty do
    throwError "axiom audit: {name} depends on unapproved axioms {unexpected.toList}"

/-- Audit all safe declarations in a namespace, including certificate definitions,
constructors, and private declarations. Unsafe/partial metaprograms are not proof
evidence; any axiom they introduce into a safe declaration is still rejected. -/
def checkNamespace (namespaceName : Name) : CoreM Nat := do
  let environment ← getEnv
  let mut count := 0
  for (name, info) in environment.constants.toList do
    let userName := privateToUserName? name |>.getD name
    if namespaceName.isPrefixOf userName && !info.isUnsafe && !info.isPartial then
      checkDeclaration name
      count := count + 1
  if count == 0 then
    throwError "axiom audit: no declarations in namespace {namespaceName}"
  pure count

open Elab Command in
elab "#veripy_audit " namespaceName:ident : command => do
  let count ← liftCoreM (checkNamespace namespaceName.getId)
  logInfo m!"Axiom audit passed: {count} declarations in {namespaceName.getId}; only standard Lean axioms"

end VeriPyAsm.Verification.AxiomAudit
