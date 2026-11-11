import VeriPyAsm.Examples.SourceNestedCheckpoints.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! Entry, invariant, and ranking proofs shared by both checkpoint providers. -/

namespace VeriPyAsm.Examples.SourceNestedCheckpoints

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

#veripy_audit VeriPyAsm.Examples.SourceNestedCheckpoints
end VeriPyAsm.Examples.SourceNestedCheckpoints
