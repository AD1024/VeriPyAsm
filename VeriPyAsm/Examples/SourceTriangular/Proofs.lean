import VeriPyAsm.Examples.SourceTriangular.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! User-owned proofs for a specification generated entirely from Python source
annotations. This imports no manual triangular block summaries or specifications.
-/

namespace VeriPyAsm.Examples.SourceTriangular

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n _
  exact ⟨[.int n], rfl, rfl⟩

@[veripy_proof generated.VC.init]
theorem init : generated.VC.init := by
  simp [generated.VC.init]

@[veripy_proof generated.VC.cut6]
theorem preserve : generated.VC.cut6 := by
  intro n _ current _ counter sum _ nonnegative equation
  split
  · grind
  · have zero : counter = 0 := by omega
    subst counter
    simpa using equation

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : Verification.ArtifactTotalCorrect artifact contract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl

#veripy_audit VeriPyAsm.Examples.SourceTriangular

end VeriPyAsm.Examples.SourceTriangular
