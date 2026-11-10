import VeriPyAsm.Examples.SourceNestedCheckpoints.MainProofs
import VeriPyAsm.Automation.Crush

/-! Checked automation for the same mandatory nested checkpoint obligations. -/

namespace VeriPyAsm.Examples.SourceNestedCheckpoints.CrushProofs

veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[3]!.provider = "crush" := rfl
example : verified.report.obligations[5]!.provider = "crush" := rfl
example : verified.report.obligations[5]!.actualBackend = some "cvc5" := rfl

#eval show Lean.CoreM Unit from do
  for name in [`VeriPyAsm.Examples.SourceNestedCheckpoints.runtimeAssertion,
      `VeriPyAsm.Examples.SourceNestedCheckpoints.outerConserved] do
    if (← Lean.getEnv).contains name then
      throwError "nested checkpoint Crush example imports the manual provider {name}"

#veripy_audit VeriPyAsm.Examples.SourceNestedCheckpoints.CrushProofs
end VeriPyAsm.Examples.SourceNestedCheckpoints.CrushProofs
