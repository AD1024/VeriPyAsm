import VeriPyAsm.Verification.VC.Generate
import VeriPyAsm.Verification.VC.Discharge
import VeriPyAsm.Examples.Assertions.Artifact

namespace VeriPyAsm.Tests.GeneratedCheckpoint
open Semantics Verification Examples

def base : VC.Specification Int where
  contract := {
    pre := fun n initial => 0 ≤ n ∧ initial = { locals := [some (.int n)] }
    post := fun n _ value _ => value = .int n
    raises := fun _ _ _ _ => False }

def assertion : VC.EdgeCheckpoint Int where
  label := "assertion"
  kind := "runtime_assertion"
  edges := [(0, 2)]
  claim next _ _ current := VC.Checkpoint.assertionPass next [20] 10 current

def hint : VC.EdgeCheckpoint Int where
  label := "hint"
  edges := [(10, 20)]
  claim _ n _ _ := 1 ≤ n + 1

def specification : VC.CheckpointSpecification Int := ⟨base, [assertion, hint]⟩

veripy_generate generated from Assertions.nonnegative for specification unfolding [base, assertion, hint]

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n _
  exact ⟨[.int n], rfl, rfl⟩
@[veripy_proof generated.VC.init]
theorem init : generated.VC.init := True.intro
@[veripy_proof generated.VC.checkpoint_assertion]
theorem assertionProof : generated.VC.checkpoint_assertion := True.intro
@[veripy_proof generated.VC.checkpoint_hint]
theorem hintProof : generated.VC.checkpoint_hint := by intro n nonnegative; omega

set_option veripy.auto false in
veripy_verify verified from generated

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[2]!.kind = "runtime_assertion" := rfl
example : verified.report.obligations[3]!.kind = "logical_checkpoint" := rfl
example : generated.VC.checkpoint_hint = (∀ n : Int, 0 ≤ n → 1 ≤ n + 1) := rfl

namespace FalseHint
def falseHint : VC.EdgeCheckpoint Int := { hint with claim := fun _ _ _ _ => False }
def spec : VC.CheckpointSpecification Int := { specification with checkpoints := [assertion, falseHint] }
veripy_generate generated from Assertions.nonnegative for spec unfolding [base, specification, assertion, falseHint, hint]

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := GeneratedCheckpoint.entry
@[veripy_proof generated.VC.init]
theorem downstream : generated.VC.init := True.intro
@[veripy_proof generated.VC.checkpoint_assertion]
theorem assertionProof : generated.VC.checkpoint_assertion := True.intro
theorem unprovable : ¬ generated.VC.checkpoint_hint := by
  intro valid
  have impossible := valid 0
  omega

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from generated
example : pending.report.complete = false := rfl
example : pending.report.obligations[1]!.status = "proved" := rfl
example : pending.report.obligations[3]!.status = "pending" := rfl

/-- error: verification incomplete: 1 unresolved VC(s); no VerifiedArtifact exported -/
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify rejected from generated
end FalseHint

def nonexistent : VC.CheckpointSpecification Int :=
  { specification with checkpoints := [{ hint with edges := [(0, 20)] }] }
/-- error: checkpoint hint uses a nonexistent decoded edge 0 -> 20 -/
#guard_msgs in
veripy_generate invalidEdge from Assertions.nonnegative for nonexistent

def duplicate : VC.CheckpointSpecification Int := { specification with checkpoints := [hint, hint] }
/-- error: empty or duplicate checkpoint label: hint -/
#guard_msgs in
veripy_generate invalidLabels from Assertions.nonnegative for duplicate

def collision.VC.checkpoint_hint : Prop := True
/-- error: (kernel) constant has already been declared 'VeriPyAsm.Tests.GeneratedCheckpoint.collision.VC.checkpoint_hint' -/
#guard_msgs in
veripy_generate collision from Assertions.nonnegative for specification unfolding [base, assertion, hint]

run_cmd Lean.Elab.Command.liftTermElabM do
  for name in [`invalidEdge, `invalidLabels, `collision, `FalseHint.rejected] do
    for suffix in [Lean.Name.anonymous, `program, `VC.entry, `Proofs, `assemble, `report] do
      let full := `VeriPyAsm.Tests.GeneratedCheckpoint ++ name ++ suffix
      if (← Lean.getEnv).contains full then throwError "failed checkpoint command retained {full}"
  let manifest ← VC.getManifest ``generated
  for obligation in manifest.obligations do
    let statement ← VC.goalStatement obligation.goal
    let .ok parsed := Lean.Parser.runParserCategory (← Lean.getEnv) `term statement
      | throwError "checkpoint VC handoff does not parse"
    let expression ← Lean.Elab.Term.elabType parsed
    unless (← Lean.Meta.isDefEq expression (Lean.mkConst obligation.goal)) do
      throwError "checkpoint VC handoff changed its exact theorem"
    discard <| VC.audit (obligation.goal ++ `normalization) .checked

#veripy_audit VeriPyAsm.Tests.GeneratedCheckpoint
end VeriPyAsm.Tests.GeneratedCheckpoint
