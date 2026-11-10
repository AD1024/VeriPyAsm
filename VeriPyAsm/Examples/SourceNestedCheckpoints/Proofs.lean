import VeriPyAsm.Examples.SourceNestedCheckpoints.MainProofs

/-! Exact providers for checkpoints before, inside, and after the inner loop. -/

namespace VeriPyAsm.Examples.SourceNestedCheckpoints

set_option maxHeartbeats 8000000

@[veripy_proof generated.VC.checkpoint_inner_initialized]
theorem innerInitialized : generated.VC.checkpoint_inner_initialized := by
  unfold generated.VC.checkpoint_inner_initialized
  grind

@[veripy_proof generated.VC.checkpoint_remaining_nonnegative]
theorem runtimeAssertion : generated.VC.checkpoint_remaining_nonnegative := by
  unfold generated.VC.checkpoint_remaining_nonnegative
  grind

@[veripy_proof generated.VC.checkpoint_inner_conserved]
theorem innerConserved : generated.VC.checkpoint_inner_conserved := by
  unfold generated.VC.checkpoint_inner_conserved
  grind

@[veripy_proof generated.VC.checkpoint_outer_conserved]
theorem outerConserved : generated.VC.checkpoint_outer_conserved := by
  unfold generated.VC.checkpoint_outer_conserved
  grind

@[veripy_proof generated.VC.checkpoint_product]
theorem product : generated.VC.checkpoint_product := by
  unfold generated.VC.checkpoint_product
  grind

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations.size = 7 := rfl
example : verified.report.obligations[3]!.kind = "runtime_assertion" := rfl
example : verified.report.obligations[5]!.provider = "manual" := rfl

#veripy_audit VeriPyAsm.Examples.SourceNestedCheckpoints
end VeriPyAsm.Examples.SourceNestedCheckpoints
