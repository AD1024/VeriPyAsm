import VeriPyAsm.Verification.VC.ScopedCheckpoint
import VeriPyAsm.Verification.AxiomAudit

namespace VeriPyAsm.Tests.ScopedCheckpoint
open Semantics Verification VC

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private def next (s : Frame) : StepResult :=
  if s.pc < 3 then .next { s with pc := s.pc + 1 }
  else .halted (.returned (.int 0) s)

private def outer : ScopedLoop Unit where
  header := 0
  exits := [3]
  invariant _ _ entry current := current = entry
  ranking := some (fun _ _ _ => 0)

private def inner : ScopedLoop Unit := { outer with header := 1, exits := [2] }
private def post : Postcondition := { returned := fun _ _ => True }
private def hint (edge : Nat × Nat) (claim : Prop) : EdgeCheckpoint Unit where
  label := "hint"
  edges := [edge]
  claim _ _ _ _ := claim

-- A summary exposing its exit continuation, independently of loop arithmetic.
private def summary : Summary := fun _ post entry => post.continues { entry with pc := 2 }

private def view (edge : Nat × Nat) (claim : Prop)
    (selected : Option (Fin ([hint edge claim]).length)) : Prop :=
  Checkpoint.regionWP next [hint edge claim] () {} selected [1] summary [] post 4 {}

attribute [local simp] view summary next outer inner post hint List.finRange_succ
  Checkpoint.regionWP Checkpoint.iterationRegionWP Checkpoint.loopSummary
  Checkpoint.bodyPost Checkpoint.edgeChecks Checkpoint.guard Checkpoint.terminal
  requirement findLoop ScopedLoop.atHeader ScopedLoop.rank Postcondition.Accepts

-- The selected view must follow the continuation after a summary.
-- The main view can assume a pending false claim, but its own VC refutes it.
example : view (2, 3) False none := by simp
example : ¬ view (2, 3) False (some ⟨0, by decide⟩) := by simp

-- First entry is a real edge. A loop body retains its exit continuation in a
-- selected view, rather than replacing that continuation with True.
example : ¬ view (0, 1) False (some ⟨0, by decide⟩) := by simp
example : ¬ (Checkpoint.bodyPost (checks := [hint (2, 3) False]) (some ⟨0, by decide⟩)
    inner .totalCorrectness () {} { pc := 1 } { pc := 1 } [2]
    { continues := fun _ => False }).continues { pc := 2 } := by simp

-- A true claim at a summary exit requires no independent rank decrease.
example (selected : Option (Fin ([hint (2, 3) True]).length)) : view (2, 3) True selected := by
  cases selected <;> simp

theorem reassembled : VC.regionWP next [1] summary [] post 4 {} := by
  apply Checkpoint.regionWP_sound (checks := [hint (2, 3) True]) (ghost := ()) (initial := {})
    (summaries := fun _ => summary)
    (fun _ _ _ merge entry valid => merge.continues { entry with pc := 2 } valid)
    (posts := fun _ => post) ⟨fun _ all => all none, fun _ allowed => allowed⟩
  intro selected
  change view (2, 3) True selected
  cases selected <;> simp

example : ¬ Checkpoint.regionWP next [hint (2, 3) True] () {} none [0, 1]
    (fun _ _ _ => True) [] post 0 {} := by simp

example : ¬ Checkpoint.loopSummary next [hint (2, 3) True] [outer, inner]
    .totalCorrectness () {} none 4 0 [] post {} := by simp

-- A header cut cannot hide a fault in the required first instruction.
example : ¬ Checkpoint.iterationRegionWP (fun s => .halted (.fault .stackUnderflow s))
    [hint (0, 0) True] () {} none [0] (fun _ _ _ => True) [0]
    { continues := fun _ => True } 1 {} := by simp

private def cycling : ScopedLoop Unit := { outer with exits := [1], invariant := fun _ _ _ current => current = {} }

-- A hint does not turn a zero ranking decrease into termination. Partial
-- correctness still permits this actual infinite loop.
example : ¬ Checkpoint.loopSummary (fun s => .next s) [hint (0, 0) True] [cycling]
    .totalCorrectness () {} none 1 1 [] post {} := by simp [cycling]

example : Checkpoint.loopSummary (fun s => .next s) [hint (0, 0) True] [cycling]
    .partialCorrectness () {} none 1 1 [] post {} := by
  simp [cycling]
  intro current _ equal
  subst current
  simp

#veripy_audit VeriPyAsm.Tests.ScopedCheckpoint
#veripy_audit VeriPyAsm.Verification.VC.ScopedCheckpointSpecification
end VeriPyAsm.Tests.ScopedCheckpoint
