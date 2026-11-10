import VeriPyAsm.Examples.SourceNestedCheckpoints.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! Entry, invariant, and ranking proofs shared by both checkpoint providers. -/

namespace VeriPyAsm.Examples.SourceNestedCheckpoints

set_option maxHeartbeats 8000000

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n m _ _ _ _
  exact ⟨[.int n, .int m], rfl, rfl⟩

@[veripy_proof generated.VC.execution]
theorem execution : generated.VC.execution := by
  unfold generated.VC.execution
  grind

#veripy_audit VeriPyAsm.Examples.SourceNestedCheckpoints
end VeriPyAsm.Examples.SourceNestedCheckpoints
