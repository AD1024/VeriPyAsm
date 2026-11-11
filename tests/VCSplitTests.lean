import VeriPyAsm.Verification.VC.Split

namespace VeriPyAsm.Tests.VCSplit
open Verification.VC

-- A false inner measure must not become an assumption used to prove an
-- unrelated outer invariant or exit. Branch assumptions remain local.
def combined : Prop := ∀ n : Nat, 0 < n →
  requirement 10 .initialization (0 ≤ n) ∧
  (if n = 1 then requirement 28 .ranking (n < n)
   else requirement 28 .preservation (1 ≤ n)) ∧
  requirement 28 .exit (requirement 10 .ranking (n - 1 < n) ∧
    requirement 10 .exit (0 ≤ n))

run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Generation.scopedParts `VeriPyAsm.Tests.VCSplit.generated ``combined #[10, 28] true

theorem initialization : generated.VC.loop_10_init := by
  unfold generated.VC.loop_10_init; grind
theorem preservation : generated.VC.loop_28_preservation := by
  unfold generated.VC.loop_28_preservation; grind
theorem outerRanking : generated.VC.loop_10_ranking := by
  unfold generated.VC.loop_10_ranking; grind
theorem outerExit : generated.VC.loop_10_exit := by
  unfold generated.VC.loop_10_exit; grind
theorem badRanking : ¬ generated.VC.loop_28_ranking := by
  intro valid
  have impossible := valid 1 (by decide) rfl
  omega

-- Reconstruction requires precisely the separate parts, including the
-- otherwise unprovable rank. It remains a conditional, audited theorem.
example (rank : generated.VC.loop_28_ranking) : combined :=
  generated.execution_of_parts True.intro initialization True.intro outerRanking
    outerExit True.intro preservation rank True.intro

def dependent : Prop := ∀ n : Nat, if h : 0 < n then
  requirement 10 .preservation (n - 1 < n ∧ h = h)
  else requirement 10 .exit (n = 0)

run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Generation.scopedParts `VeriPyAsm.Tests.VCSplit.dependentSplit ``dependent #[10] false

theorem dependentReconstructed : dependent := by
  apply dependentSplit.execution_of_parts True.intro True.intro
  · unfold dependentSplit.VC.loop_10_preservation; grind
  · unfold dependentSplit.VC.loop_10_exit; grind

-- Do not silently erase a requirement under an unsupported connective.
def unsupported : Prop := requirement 10 .ranking False ∨ True
/-- error: unsupported logical form around a scoped requirement: requirement 10 RequirementKind.ranking False ∨ True -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Generation.scopedParts `VeriPyAsm.Tests.VCSplit.rejected ``unsupported #[10] true

run_cmd do
  if (← Lean.getEnv).contains `VeriPyAsm.Tests.VCSplit.rejected.execution_of_parts then
    throwError "unsupported split exported a reconstruction"

#veripy_audit VeriPyAsm.Tests.VCSplit
end VeriPyAsm.Tests.VCSplit
