import VeriPyAsm.Examples.Triangular.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! An ordinary Lean provider for automatically generated obligations. This
module proves arithmetic and entry compatibility; it contains no execution or
whole-program assembly proof. The optional Crush provider is independent. -/

namespace VeriPyAsm.Examples.Triangular.GeneratedProofs

open Semantics Verification

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro N _
  exact ⟨[.int N], rfl, rfl⟩

@[veripy_proof generated.VC.init]
theorem init : generated.VC.init := True.intro

@[veripy_proof generated.VC.cut6]
theorem cut6 : generated.VC.cut6 := by
  intro N _ current _ n sum _ nonnegative equation
  split
  · exact ⟨by omega, by grind, by omega⟩
  · have zero : n = 0 := by omega
    subst n
    simpa using equation

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : ArtifactTotalCorrect triangularArtifact triangularContract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl

#veripy_audit VeriPyAsm.Examples.Triangular.GeneratedProofs

end VeriPyAsm.Examples.Triangular.GeneratedProofs
