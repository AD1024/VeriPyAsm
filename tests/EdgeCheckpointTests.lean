import VeriPyAsm.Verification.VC.EdgeCheckpoint
import VeriPyAsm.Verification.AxiomAudit

namespace VeriPyAsm.Tests.EdgeCheckpoint
open Semantics Verification VC
attribute [local simp] List.finRange_succ

private def returning : Frame → StepResult := fun s =>
  if s.pc = 0 then .next { s with pc := 1 }
  else .halted (.returned (.int 0) s)

private def accepted : Postcondition := { returned := fun _ _ => True }

private def falseHint : EdgeCheckpoint Unit where
  label := "false_hint"
  edges := [(0, 1)]
  claim _ _ _ _ := False

-- The main VC can use a pending hint. Its own incoming VC cannot use itself.
example : Checkpoint.wp returning [falseHint] () {} none [] accepted 2 {} := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, returning, falseHint]

example : ¬ Checkpoint.wp returning [falseHint] () {} (some ⟨0, by decide⟩) [] accepted 2 {} := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, returning, falseHint]

-- Later same-edge hints may use earlier ones, but cannot prove them backwards.
example : ¬ Checkpoint.wp returning [falseHint, falseHint] () {}
    (some ⟨0, by decide⟩) [] accepted 2 {} := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, returning, falseHint]

example : Checkpoint.wp returning [falseHint, falseHint] () {}
    (some ⟨1, by decide⟩) [] accepted 2 {} := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, returning, falseHint]

private def otherBranch : Frame → StepResult := fun s =>
  if s.pc = 2 then .next { s with pc := 3 }
  else .halted (.returned (.int 0) s)

private def branchHint : EdgeCheckpoint Unit := { falseHint with edges := [(1, 3)] }

-- Sharing a destination PC does not make an unrelated branch assume the hint.
example : Checkpoint.wp otherBranch [branchHint] () {} none [] accepted 2 { pc := 2 } := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.terminal,
    otherBranch, branchHint, accepted, Postcondition.Accepts]

example : Checkpoint.wp otherBranch [branchHint] () {} (some ⟨0, by decide⟩) [] accepted 2 { pc := 2 } := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.terminal,
    otherBranch, branchHint]

private def changed : Frame → StepResult := fun _ => .next { pc := 1, locals := [some (.int 1)] }
private def stale : EdgeCheckpoint Unit where
  label := "stale"
  edges := [(0, 1)]
  claim _ _ _ current := current.locals = [some (.int 0)]

example : ¬ Checkpoint.wp changed [stale] () {} (some ⟨0, by decide⟩) [1]
    { continues := fun _ => True } 1 { locals := [some (.int 0)] } := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, stale, changed]

-- A logical hint adds no fuel, no VM step, and no escape from faults/ranking.
private def trueHint : EdgeCheckpoint Unit := { falseHint with claim := fun _ _ _ _ => True }
example : ¬ Checkpoint.wp returning [trueHint] () {} none [] accepted 1 {} := by
  simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, Checkpoint.terminal, trueHint, falseHint, returning]

example : ¬ Checkpoint.iterationWP (fun s => .halted (.fault .stackUnderflow s))
    [trueHint] () {} none [0] { continues := fun _ => True } 1 {} := by
  simp [Checkpoint.iterationWP, Checkpoint.terminal, Postcondition.Accepts]

example : ¬ Checkpoint.iterationWP (fun s => .next { s with pc := 0 }) [trueHint] () {} none [0]
    { continues := fun _ => (0 : Nat) < 0 } 1 {} := by
  simp [Checkpoint.iterationWP, Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.terminal, trueHint, falseHint]

-- All views reassemble to the original WP, with the same exact fuel bound.
theorem reassembled : VC.wp returning [] accepted 2 {} := by
  apply Checkpoint.wp_sound (checks := [trueHint]) (ghost := ()) (initial := {})
  intro selected
  cases selected <;>
    simp [Checkpoint.wp, Checkpoint.edgeChecks, Checkpoint.guard, Checkpoint.terminal,
      trueHint, falseHint, returning, accepted, Postcondition.Accepts]

example : ¬ Checkpoint.assertionPass (fun s => .halted (.raised .assertionError s)) [] 1 {} := by
  simp [Checkpoint.assertionPass, VC.wp, Postcondition.Accepts]

#veripy_audit VeriPyAsm.Tests.EdgeCheckpoint
end VeriPyAsm.Tests.EdgeCheckpoint
