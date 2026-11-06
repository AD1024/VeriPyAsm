import VeriPyAsm.Examples.Triangular.Generated
import VeriPyAsm.Automation.Crush

/-! Checked discharge of automatically generated VCs. The supplied cutpoint
proof normalizes the Nat ranking with omega and sends its integer arithmetic
to Crush. No hand-written execution or assembly module is imported. -/

namespace VeriPyAsm.Examples.Triangular.GeneratedCrush

open Semantics Verification

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro N _
  exact ⟨[.int N], rfl, rfl⟩

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.timeout 5
set_option crush.reconstruct.trustBvDecide false
set_option crush.reconstruct.trustNativeDecide false

@[veripy_proof generated.VC.cut6]
theorem cut6 : generated.VC.cut6 := by
  intro N _ current _ n sum _ nonnegative equation
  split
  · refine ⟨?_, ?_, by omega⟩ <;> crush
  · crush

veripy_verify verified from generated

theorem artifact_total : ArtifactTotalCorrect triangularArtifact triangularContract :=
  verified.artifact_total

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[0]!.provider = "manual" := rfl
example : verified.report.obligations[1]!.provider = "crush" := rfl
example : verified.report.obligations[2]!.provider = "manual" := rfl

#eval show Lean.CoreM Unit from do
  for name in [`VeriPyAsm.Examples.Triangular.Assembly.verified,
      `VeriPyAsm.Examples.Triangular.Arithmetic.proofs,
      `VeriPyAsm.Examples.Triangular.GeneratedProofs.verified] do
    if (← Lean.getEnv).contains name then
      throwError "generated Crush example unexpectedly imports {name}"

#veripy_audit VeriPyAsm.Examples.Triangular.GeneratedCrush

end VeriPyAsm.Examples.Triangular.GeneratedCrush
