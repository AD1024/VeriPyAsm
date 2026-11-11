"""Test-only manual providers for the dynamically named scoped obligations."""

import json


def scoped_providers(exclude=()):
    excluded = ", ".join(json.dumps(field) for field in exclude)
    return f'''
set_option Elab.async false in
run_cmd do
  let manifest ← Lean.Elab.Command.liftCoreM <| VeriPyAsm.Verification.VC.getManifest ``generated
  for obligation in manifest.obligations do
    if obligation.field == `entry || obligation.field.toString.startsWith "checkpoint_" ||
        (#[{excluded}] : Array String).contains obligation.field.toString then continue
    let goal := Lean.mkIdent obligation.goal
    let provider := Lean.mkIdent (Lean.Name.mkSimple ("proof_" ++ obligation.field.toString))
    Lean.Elab.Command.elabCommand (← `(command|
      @[veripy_proof $goal:ident]
      theorem $provider:ident : $goal:ident := by unfold $goal:ident; grind))
'''
