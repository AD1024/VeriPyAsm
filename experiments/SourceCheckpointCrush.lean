import VeriPyAsm.Examples.SourceCheckpoints.MainProofs
import VeriPyAsm.Automation.Crush

/-! The same generated specification, with both incoming checkpoint obligations
discharged by checked Crush automation rather than importing manual providers. -/

namespace VeriPyAsm.Examples.SourceCheckpoints.CrushProofs

veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[3]!.provider = "crush" := rfl
example : verified.report.obligations[4]!.provider = "crush" := rfl
example : verified.report.obligations[4]!.actualBackend = some "cvc5" := rfl

#eval show Lean.CoreM Unit from do
  for name in [`VeriPyAsm.Examples.SourceCheckpoints.runtimeAssertion,
      `VeriPyAsm.Examples.SourceCheckpoints.conserved] do
    if (← Lean.getEnv).contains name then
      throwError "source checkpoint Crush example imports the manual provider {name}"

#veripy_audit VeriPyAsm.Examples.SourceCheckpoints.CrushProofs
end VeriPyAsm.Examples.SourceCheckpoints.CrushProofs
