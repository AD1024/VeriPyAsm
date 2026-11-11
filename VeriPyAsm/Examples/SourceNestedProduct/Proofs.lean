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

@[veripy_proof generated.VC.safety]
theorem safety : generated.VC.safety := by
  unfold generated.VC.safety
  grind

@[veripy_proof generated.VC.loop_10_init]
theorem loop_10_init : generated.VC.loop_10_init := by
  unfold generated.VC.loop_10_init
  grind

@[veripy_proof generated.VC.loop_10_preservation]
theorem loop_10_preservation : generated.VC.loop_10_preservation := by
  unfold generated.VC.loop_10_preservation
  grind

@[veripy_proof generated.VC.loop_10_ranking]
theorem loop_10_ranking : generated.VC.loop_10_ranking := by
  unfold generated.VC.loop_10_ranking
  grind

@[veripy_proof generated.VC.loop_10_exit]
theorem loop_10_exit : generated.VC.loop_10_exit := by
  unfold generated.VC.loop_10_exit
  grind

@[veripy_proof generated.VC.loop_28_init]
theorem loop_28_init : generated.VC.loop_28_init := by
  unfold generated.VC.loop_28_init
  grind

@[veripy_proof generated.VC.loop_28_preservation]
theorem loop_28_preservation : generated.VC.loop_28_preservation := by
  unfold generated.VC.loop_28_preservation
  grind

@[veripy_proof generated.VC.loop_28_ranking]
theorem loop_28_ranking : generated.VC.loop_28_ranking := by
  unfold generated.VC.loop_28_ranking
  grind

@[veripy_proof generated.VC.loop_28_exit]
theorem loop_28_exit : generated.VC.loop_28_exit := by
  unfold generated.VC.loop_28_exit
  grind

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl

#veripy_audit VeriPyAsm.Examples.SourceNestedProduct

end VeriPyAsm.Examples.SourceNestedProduct
