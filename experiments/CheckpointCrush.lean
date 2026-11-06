import VeriPyAsm.Examples.Checkpoints.Segments
import VeriPyAsm.Automation.Crush

/-! An alternate provider for the same checkpoint manifest. Instruction safety
comes from checked segment proofs; Crush discharges the separate incoming hint.
-/

namespace VeriPyAsm.Examples.Checkpoints.CrushProofs

open Verification

@[veripy_proof VC.entry]
theorem entry : VC.entry := Segments.entry

@[veripy_proof VC.runtimeAssertion]
theorem runtimeAssertion : VC.runtimeAssertion := Segments.runtimeAssertion

@[veripy_proof VC.finish]
theorem finish : VC.finish := Segments.finish

veripy_verify verified from obligations

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[2]!.provider = "crush" := rfl

#eval show Lean.CoreM Unit from do
  unless !(← Lean.getEnv).contains `VeriPyAsm.Examples.Checkpoints.hint do
    throwError "Crush checkpoint example imports the manual hint provider"

#veripy_audit VeriPyAsm.Examples.Checkpoints.CrushProofs

end VeriPyAsm.Examples.Checkpoints.CrushProofs
