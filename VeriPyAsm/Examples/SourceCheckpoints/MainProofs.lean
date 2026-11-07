import VeriPyAsm.Examples.SourceCheckpoints.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! Common entry, invariant, and ranking proofs. Assertion and hint obligations
remain separate mandatory fields, supplied by the manual or Crush provider. -/

namespace VeriPyAsm.Examples.SourceCheckpoints

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
  · intros
    omega
  · have zero : counter = 0 := by omega
    subst counter
    simpa using equation

#veripy_audit VeriPyAsm.Examples.SourceCheckpoints
end VeriPyAsm.Examples.SourceCheckpoints
