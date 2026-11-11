import VeriPyAsm.Verification.VC.Generate
import VeriPyAsm.Verification.VC.Discharge
import VeriPyAsm.Examples.Assertions.Artifact

namespace VeriPyAsm.Tests.GeneratedScopedCheckpoint
open Semantics Verification Examples

def base : VC.ScopedSpecification Int where
  contract := {
    pre := fun n initial => 0 ≤ n ∧ initial = { locals := [some (.int n)] }
    post := fun n _ value _ => value = .int n
    raises := fun _ _ _ _ => False }
  loops := []

def assertion : VC.EdgeCheckpoint Int where
  label := "assertion"
  kind := "runtime_assertion"
  edges := [(0, 2)]
  claim next _ _ current := VC.Checkpoint.assertionPass next [20] 10 current

def hint : VC.EdgeCheckpoint Int where
  label := "hint"
  edges := [(10, 20)]
  claim _ n _ _ := 1 ≤ n + 1

def specification : VC.ScopedCheckpointSpecification Int := ⟨base, [assertion, hint]⟩

veripy_generate generated from Assertions.nonnegative for specification unfolding [base, assertion, hint]

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n _
  exact ⟨[.int n], rfl, rfl⟩
@[veripy_proof generated.VC.safety]
theorem execution : generated.VC.safety := True.intro
@[veripy_proof generated.VC.checkpoint_assertion]
theorem assertionProof : generated.VC.checkpoint_assertion := True.intro
@[veripy_proof generated.VC.checkpoint_hint]
theorem hintProof : generated.VC.checkpoint_hint := by intro n nonnegative; omega

set_option veripy.auto false in
veripy_verify verified from generated
example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[1]!.kind = "execution_safety" := rfl

namespace FalseHint
def falseHint : VC.EdgeCheckpoint Int := { hint with claim := fun _ _ _ _ => False }
def spec : VC.ScopedCheckpointSpecification Int := { specification with checkpoints := [assertion, falseHint] }
veripy_generate generated from Assertions.nonnegative for spec unfolding [base, specification, assertion, falseHint, hint]

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := GeneratedScopedCheckpoint.entry
@[veripy_proof generated.VC.safety]
theorem downstream : generated.VC.safety := True.intro
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

def missingRank : VC.ScopedCheckpointSpecification Int :=
  { specification with base := { base with loops := [{ header := 0, exits := [20], invariant := fun _ _ _ _ => True }] } }
/-- error: total correctness requires a ranking function for every scoped loop -/
#guard_msgs in
veripy_generate invalidRank from Assertions.nonnegative for missingRank

def nonexistent : VC.ScopedCheckpointSpecification Int :=
  { specification with checkpoints := [{ hint with edges := [(0, 20)] }] }
/-- error: checkpoint hint uses a nonexistent decoded edge 0 -> 20 -/
#guard_msgs in
veripy_generate invalidEdge from Assertions.nonnegative for nonexistent

run_cmd Lean.Elab.Command.liftTermElabM do
  for name in [`invalidRank, `invalidEdge, `FalseHint.rejected] do
    for suffix in [Lean.Name.anonymous, `program, `VC.entry, `Proofs, `assemble, `report] do
      let full := `VeriPyAsm.Tests.GeneratedScopedCheckpoint ++ name ++ suffix
      if (← Lean.getEnv).contains full then throwError "failed scoped checkpoint command retained {full}"
  let manifest ← VC.getManifest ``generated
  for obligation in manifest.obligations do
    let statement ← VC.goalStatement obligation.goal
    let .ok parsed := Lean.Parser.runParserCategory (← Lean.getEnv) `term statement
      | throwError "scoped checkpoint handoff does not parse"
    let expression ← Lean.Elab.Term.elabType parsed
    unless (← Lean.Meta.isDefEq expression (Lean.mkConst obligation.goal)) do
      throwError "scoped checkpoint handoff changed its theorem"
    discard <| VC.audit (obligation.goal ++ `normalization) .checked

#veripy_audit VeriPyAsm.Tests.GeneratedScopedCheckpoint
end VeriPyAsm.Tests.GeneratedScopedCheckpoint
