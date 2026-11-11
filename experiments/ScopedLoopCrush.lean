import VeriPyAsm.Examples.SourceNestedProduct.Generated
import VeriPyAsm.Automation.Crush

/-! Independent providers for scoped loop VCs. Crush proves initialization,
preservation, and exits; explicit kernel proofs handle the Int.toNat measures.
Import only the generated declarations so no manual invariant provider leaks in. -/

namespace VeriPyAsm.Examples.SourceNestedProduct.CrushProofs

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n m _ _ _ _
  exact ⟨[.int n, .int m], rfl, rfl⟩

@[veripy_proof generated.VC.loop_10_ranking]
theorem outerRanking : generated.VC.loop_10_ranking := by
  unfold generated.VC.loop_10_ranking
  grind

@[veripy_proof generated.VC.loop_28_ranking]
theorem innerRanking : generated.VC.loop_28_ranking := by
  unfold generated.VC.loop_28_ranking
  grind

veripy_verify verified from generated

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[3]!.provider = "crush" := rfl
example : verified.report.obligations[3]!.actualBackend = some "cvc5" := rfl
example : verified.report.obligations[7]!.provider = "crush" := rfl
example : verified.report.obligations[8]!.provider = "manual" := rfl

#veripy_audit VeriPyAsm.Examples.SourceNestedProduct.CrushProofs
end VeriPyAsm.Examples.SourceNestedProduct.CrushProofs
