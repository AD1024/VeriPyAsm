import VeriPyAsm.Examples.Checkpoints

/-! A downstream proof conditional on a hint is not permission to omit that
hint's incoming VC. Check strict rollback, discovery, exact handoff, and the
final package's execution on the original admitted assertion bytes.
-/

namespace VeriPyAsm.Tests.CheckpointVC

open Semantics Verification Examples

example : Checkpoints.verified.report.complete = true := rfl
example : Checkpoints.verified.report.assurance = some "checked" := rfl
example : Checkpoints.verified.report.obligations.size = 4 := rfl
example : Checkpoints.verified.report.obligations[1]!.kind = "runtime_assertion" := rfl
example : Checkpoints.verified.report.obligations[2]!.kind = "logical_checkpoint" := rfl
example : Checkpoints.verified.report.obligations[2]!.provider = "manual" := rfl
example : Checkpoints.VC.hint = (∀ n : Int, 0 ≤ n → 1 ≤ n + 1) := rfl

namespace FalseHint

def entry : Prop := Checkpoints.VC.entry
def runtimeAssertion : Prop := Checkpoints.VC.runtimeAssertion
def hint : Prop := Checkpoints.hintVC (fun _ => False)
def finish : Prop := Checkpoints.finishVC (fun _ => False)

structure Proofs : Prop where
  entry : entry
  runtimeAssertion : runtimeAssertion
  hint : hint
  finish : finish

def assemble (proofs : Proofs) : VerifiedArtifact Assertions.nonnegativeArtifact Checkpoints.contract :=
  Checkpoints.assembleUsing (fun _ => False) proofs.entry proofs.runtimeAssertion proofs.hint proofs.finish

veripy_vcs obligations : VerifiedArtifact Assertions.nonnegativeArtifact Checkpoints.contract via assemble where
  entry : entry at 0 vc_kind "entry_compatibility"
  runtimeAssertion : runtimeAssertion at 2 vc_kind "runtime_assertion"
  hint : hint at 20 vc_kind "logical_checkpoint"
  finish : finish at 20 vc_kind "normal_exit"

@[veripy_proof entry]
theorem entryProof : entry := Checkpoints.entry

@[veripy_proof runtimeAssertion]
theorem assertionProof : runtimeAssertion := Checkpoints.runtimeAssertion

-- All downstream obligations can be proved under the false hint. They cannot
-- prove the hint itself or authorize a final package through this manifest.
@[veripy_proof finish]
theorem downstreamProof : finish := by
  rintro n current ⟨_, impossible⟩
  exact impossible.elim

theorem false_hint_is_unprovable : ¬ hint := by
  intro valid
  exact valid 0 { pc := 20, locals := [some (.int 0)] } ⟨rfl, Int.le_refl 0⟩

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from obligations

example : pending.report.complete = false := rfl
example : pending.report.finalDeclaration = none := rfl
example : pending.report.obligations[1]!.status = "proved" := rfl
example : pending.report.obligations[2]!.status = "pending" := rfl
example : pending.report.obligations[3]!.status = "proved" := rfl

/-- error: verification incomplete: 1 unresolved VC(s); no VerifiedArtifact exported -/
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify rejected from obligations

#eval show Lean.CoreM Unit from do
  for name in [`VeriPyAsm.Tests.CheckpointVC.FalseHint.rejected,
      `VeriPyAsm.Tests.CheckpointVC.FalseHint.rejected.vc.runtimeAssertion,
      `VeriPyAsm.Tests.CheckpointVC.FalseHint.rejected.report] do
    if (← Lean.getEnv).contains name then throwError "unproved checkpoint exported {name}"

end FalseHint

-- The handoff preserves the complete statement, including its incoming context.
run_cmd Lean.Elab.Command.liftTermElabM do
  let statement ← VC.goalStatement ``Checkpoints.VC.hint
  let .ok term := Lean.Parser.runParserCategory (← Lean.getEnv) `term statement
    | throwError "checkpoint handoff does not parse"
  let type ← Lean.Elab.Term.elabType term
  unless (← Lean.Meta.isDefEq type (Lean.mkConst ``Checkpoints.VC.hint)) do
    throwError "checkpoint handoff changed the exact obligation"

#eval show IO Unit from do
  let observed := run (step Checkpoints.verified.admission.translation.program) 7
    { locals := [some (.int 0)] }
  unless observed == .halted (.returned (.int 0) { pc := 22, locals := [some (.int 0)] }) do
    throw <| IO.userError "checkpoint package changed assertion execution"

#veripy_audit VeriPyAsm.Tests.CheckpointVC

end VeriPyAsm.Tests.CheckpointVC
