import VeriPyAsm.Examples.SourceCheckpoints.MainProofs

/-! Exact manual providers for source-generated checkpoint obligations. -/

namespace VeriPyAsm.Examples.SourceCheckpoints

@[veripy_proof generated.VC.checkpoint_remaining_nonnegative]
theorem runtimeAssertion : generated.VC.checkpoint_remaining_nonnegative := by
  intro n _ current _ counter sum _ nonnegative equation positive
  omega

@[veripy_proof generated.VC.checkpoint_conserved]
theorem conserved : generated.VC.checkpoint_conserved := by
  intro n _ current _ counter sum _ nonnegative equation positive bounded
  grind

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[3]!.kind = "runtime_assertion" := rfl
example : verified.report.obligations[4]!.kind = "logical_checkpoint" := rfl

#veripy_audit VeriPyAsm.Examples.SourceCheckpoints
end VeriPyAsm.Examples.SourceCheckpoints
