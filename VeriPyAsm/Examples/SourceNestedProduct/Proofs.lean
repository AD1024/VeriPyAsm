import VeriPyAsm.Examples.SourceNestedProduct.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! Nested source loops with independent measures. The inner counter is first
initialized inside the outer loop, and resets on every outer iteration. -/

namespace VeriPyAsm.Examples.SourceNestedProduct

set_option maxHeartbeats 8000000

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n m _ _ _ _
  exact ⟨[.int n, .int m], rfl, rfl⟩

@[veripy_proof generated.VC.execution]
theorem execution : generated.VC.execution := by
  unfold generated.VC.execution
  grind

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl

#veripy_audit VeriPyAsm.Examples.SourceNestedProduct

end VeriPyAsm.Examples.SourceNestedProduct
