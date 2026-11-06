import VeriPyAsm.Verification.VC.Checkpoint
import VeriPyAsm.Verification.AxiomAudit

/-! Checkpoints preserve finite segment bounds, faults, first exits, and the
nonempty-iteration requirement. Facts describe the frame at the checkpoint.
-/

namespace VeriPyAsm.Tests.Checkpoint

open Semantics Verification Verification.VC

private def pushReturn (n : Int) : Program := fun pc =>
  if pc = 0 then some (Command.push 1 (.int n))
  else if pc = 1 then some Command.ret
  else none

theorem split_before_return (n : Int) (nonnegative : 0 ≤ n) :
    wp (step (pushReturn n)) []
      { returned := fun value final => value = .int n ∧ 0 ≤ n ∧ final.stack = [] }
      (1 + 1) {} := by
  apply wp_checkpoint (cuts := [1]) (prefixFuel := 1) (suffixFuel := 1)
    (context := fun s => s = { pc := 1, stack := [.int n] })
    (claim := fun _ => 0 ≤ n)
  · exact ⟨rfl, rfl⟩
  · intro _ _; exact nonnegative
  · rintro s ⟨rfl, h⟩; exact ⟨rfl, h, rfl⟩
  · intro _ impossible; cases impossible

-- The logical claim introduces no third instruction or runtime assertion.
example (n : Int) : run (step (pushReturn n)) 2 {} =
    .halted (.returned (.int n) { pc := 1 }) := rfl

theorem no_missing_incoming_fact :
    ¬ CheckpointVC (fun s => s = { pc := 1, stack := [.int (-1)] })
      (fun s => ∃ n : Int, s.stack = [.int n] ∧ 0 ≤ n) := by
  intro valid
  obtain ⟨n, equal, nonnegative⟩ := valid _ rfl
  simp only [List.cons.injEq, Value.int.injEq, and_true] at equal
  omega

private def consume : Frame → StepResult := Command.store 2 0

-- The stack fact at the checkpoint cannot be carried across a consuming write.
example : ¬ wp consume [2] { continues := fun s => s.stack = [.int 1] } 1
    { pc := 1, locals := [none], stack := [.int 1] } := by
  simp [wp, consume, Command.store]

private def fault : Frame → StepResult := fun s => .halted (.fault .stackUnderflow s)

-- Stopping at a boundary may take zero steps; a loop iteration still executes.
example : wp fault [0] { continues := fun _ => True } 0 {} := ⟨rfl, trivial⟩
example : ¬ iterationWP fault [0] { continues := fun _ => True } 0 {} := fun h => h
example : ¬ wp fault []
    { continues := fun _ => True, returned := fun _ _ => True, raises := fun _ _ => True }
    1 {} := fun h => h

-- A checkpoint alone cannot discharge an unchanged loop measure.
example : ¬ iterationWP (fun s => .next s) [0]
    { continues := fun s => s.pc < 0 } 0 {} := by simp [iterationWP, wp]

theorem early_exception_skips_hint :
    wp (fun s => .halted (.raised .typeError s)) []
      { raises := fun exception _ => exception = .typeError } (1 + 0) {} := by
  apply wp_checkpoint (cuts := [1]) (prefixFuel := 1) (suffixFuel := 0)
    (context := fun _ => False) (claim := fun _ => False)
  · exact rfl
  · intro _ impossible; exact impossible
  · intro _ impossible; exact impossible.1.elim
  · intro _ impossible; cases impossible

theorem iteration_keeps_first_step (n : Int) :
    iterationWP (step (pushReturn n)) [] { returned := fun value _ => value = .int n }
      (0 + 1) {} := by
  apply iterationWP_checkpoint (cuts := [1]) (prefixFuel := 0) (suffixFuel := 1)
    (context := fun s => s = { pc := 1, stack := [.int n] })
    (claim := fun s => s.stack = [.int n])
  · exact ⟨rfl, rfl⟩
  · rintro s rfl; rfl
  · rintro s ⟨rfl, _⟩; exact rfl
  · intro _ impossible; cases impossible

-- Checkpoint composition also works with semantic block proofs, independent of
-- the WP generator. A claim at a final exit cannot skip its first-exit behavior.
example (n : Int) :
    BlockTotalCorrect (step (pushReturn n)) (fun pc => pc = 0)
      (fun s => s = {}) { continues := fun s => s.stack = [] } := by
  apply BlockTotalCorrect.checkpoint
    (context := fun s => s = {}) (claim := fun s => s.stack = [])
    (cuts := fun pc => pc = 0)
  · exact .exit (by rintro s rfl; rfl) (fun _ h => h)
  · rintro s rfl; rfl
  · exact .exit (by rintro s ⟨rfl, _⟩; rfl) (fun _ h => h.2)
  · exact fun _ h => h

example (n : Int) :
    BlockPartialCorrect (step (pushReturn n)) (fun pc => pc = 0)
      (fun s => s = {}) { continues := fun s => s.stack = [] } := by
  have first : BlockTotalCorrect (step (pushReturn n)) (fun pc => pc = 0)
      (fun s => s = {}) { continues := fun s => s = {} } :=
    .exit (by rintro s rfl; rfl) (fun _ h => h)
  have suffix : BlockTotalCorrect (step (pushReturn n)) (fun pc => pc = 0)
      (fun s => s = {} ∧ s.stack = []) { continues := fun s => s.stack = [] } :=
    .exit (by rintro s ⟨rfl, _⟩; rfl) (fun _ h => h.2)
  exact first.partialCorrect.checkpoint (by rintro s rfl; rfl)
    suffix.partialCorrect (fun _ h => h)

#veripy_audit VeriPyAsm.Tests.Checkpoint

end VeriPyAsm.Tests.Checkpoint
