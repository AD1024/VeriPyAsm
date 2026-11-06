import VeriPyAsm.Examples.Assertions

namespace VeriPyAsm.Tests.AssertionVC

open Semantics Verification Examples.Assertions

example : ExceptionFree.verified.report.complete = true := rfl
example : ExceptionFree.verified.report.assurance = some "checked" := rfl
example : WithFailure.verified.report.complete = true := rfl
example : WithFailure.verified.report.assurance = some "checked" := rfl

def forbiddenFailure : VC.Specification Unit where
  contract := {
    pre := fun _ initial => initial = {}
    post := fun _ _ _ _ => True
    raises := fun _ _ _ _ => False }

#guard_msgs (drop info, all) in
veripy_generate failing from alwaysFails for forbiddenFailure

theorem failed_assertion_vc : ¬ failing.VC.init := by simp [failing.VC.init]

-- Stronger than failure of a sufficient VC: the actual exceptional execution
-- refutes even partial correctness and hence every final verification package.
theorem no_partial_correctness :
    ¬ ArtifactPartialCorrect alwaysFailsArtifact forbiddenFailure.contract := by
  intro correct
  have semanticCorrect := alwaysFails.translation.artifact_partial_iff.mp correct
  exact semanticCorrect.run_halted (ghost := ()) (initial := {}) rfl (fuel := 3)
    (outcome := .raised .assertionError { pc := 4, stack := [.assertionErrorType] })
    (by decide +kernel)

theorem no_verified_artifact (mode : CorrectnessMode) :
    ¬ Nonempty (VerifiedArtifact alwaysFailsArtifact forbiddenFailure.contract mode) := by
  rintro ⟨verified⟩
  exact no_partial_correctness verified.artifact_partial

@[veripy_proof failing.VC.entry]
theorem entry : failing.VC.entry := by
  exact ⟨[], rfl, rfl, rfl⟩

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from failing

example : pending.report.complete = false := rfl
example : pending.report.finalDeclaration = none := rfl
example : pending.report.obligations[0]!.provider = "manual" := rfl
example : pending.report.obligations[1]!.goal =
    "VeriPyAsm.Tests.AssertionVC.failing.VC.init" := rfl
example : pending.report.obligations[1]!.status = "pending" := rfl

/-- error: verification incomplete: 1 unresolved VC(s); no VerifiedArtifact exported -/
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify rejected from failing

#eval show Lean.CoreM Unit from do
  for name in [`VeriPyAsm.Tests.AssertionVC.rejected,
      `VeriPyAsm.Tests.AssertionVC.rejected.vc.entry,
      `VeriPyAsm.Tests.AssertionVC.rejected.report] do
    if (← Lean.getEnv).contains name then
      throwError "failed assertion exported {name}"

#veripy_audit VeriPyAsm.Tests.AssertionVC

end VeriPyAsm.Tests.AssertionVC
