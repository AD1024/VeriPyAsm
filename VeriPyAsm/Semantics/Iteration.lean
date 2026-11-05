import VeriPyAsm.Semantics.Block

/-! A nonempty execution to the next cutpoint or a halt. Unlike `BlockExecutes`,
an iteration executes its first instruction even if its entry is a cutpoint.
This separates a genuine loop back edge from the zero-step block exit. -/

namespace VeriPyAsm.Semantics

inductive IterationExecutes (next : Frame → StepResult) (cuts : Nat → Prop) :
    Frame → StepResult → Prop where
  | halt {s : Frame} {outcome : Halt} :
      next s = .halted outcome → IterationExecutes next cuts s (.halted outcome)
  | step {s s' : Frame} {result : StepResult} :
      next s = .next s' → BlockExecutes next cuts s' result →
      IterationExecutes next cuts s result

variable {next : Frame → StepResult} {cuts exits : Nat → Prop}
    {s : Frame} {result : StepResult}

theorem IterationExecutes.deterministic {other : StepResult}
    (first : IterationExecutes next cuts s result)
    (second : IterationExecutes next cuts s other) : result = other := by
  cases first with
  | halt transition =>
    cases second with
    | halt transition' => exact transition.symm.trans transition'
    | step transition' _ => cases transition.symm.trans transition'
  | step transition after =>
    cases second with
    | halt transition' => cases transition.symm.trans transition'
    | step transition' after' =>
      have equal := StepResult.next.inj (transition.symm.trans transition')
      cases equal
      exact after.deterministic after'

theorem IterationExecutes.append (contains : ∀ pc, exits pc → cuts pc)
    (outside : ¬ exits s.pc) (first : IterationExecutes next cuts s result)
    {final : StepResult}
    (suffix : match result with
      | .next middle => BlockExecutes next exits middle final
      | .halted outcome => final = .halted outcome) :
    BlockExecutes next exits s final := by
  cases first with
  | halt transition =>
    cases suffix
    exact .halt outside transition
  | step transition after =>
    cases result <;> exact .step outside transition (after.append contains suffix)

theorem BlockExecutes.split_iteration (contains : ∀ pc, exits pc → cuts pc)
    (outside : ¬ exits s.pc) (execution : BlockExecutes next exits s result) :
    ∃ middle, IterationExecutes next cuts s middle ∧
      match middle with
      | .next frame => BlockExecutes next exits frame result
      | .halted outcome => result = .halted outcome := by
  cases execution with
  | exit atExit => exact False.elim (outside atExit)
  | halt _ transition => exact ⟨_, .halt transition, rfl⟩
  | step _ transition after =>
    obtain ⟨middle, before, suffix⟩ := after.split contains
    exact ⟨middle, .step transition before, suffix⟩

/-- Reverse orientation: the successor is smaller than its predecessor.
This relation is accessible along any finite block execution, even when the
machine as a whole admits divergence. It is used only for partial soundness. -/
def BeforeExitStep (next : Frame → StepResult) (exits : Nat → Prop)
    (successor current : Frame) : Prop :=
  ¬ exits current.pc ∧ next current = .next successor

theorem BlockExecutes.accessible (execution : BlockExecutes next exits s result) :
    Acc (BeforeExitStep next exits) s := by
  induction execution with
  | exit atExit => exact .intro _ (fun _ h => False.elim (h.1 atExit))
  | halt _ transition =>
    refine .intro _ (fun _ h => ?_)
    cases transition.symm.trans h.2
  | step _ transition _ ih =>
    refine .intro _ (fun _ h => ?_)
    have equal := StepResult.next.inj (transition.symm.trans h.2)
    cases equal
    exact ih

private theorem extend_progress (contains : ∀ pc, exits pc → cuts pc)
    (execution : BlockExecutes next cuts s result) {origin : Frame}
    (before : Relation.TransGen (BeforeExitStep next exits) s origin) :
    match result with
    | .next final => Relation.TransGen (BeforeExitStep next exits) final origin
    | .halted _ => True := by
  induction execution with
  | exit => exact before
  | halt => trivial
  | @step s s' result outside transition _ ih =>
    have advance : BeforeExitStep next exits s' s :=
      ⟨fun h => outside (contains _ h), transition⟩
    cases result <;> exact ih ((Relation.TransGen.single advance).trans before)

/-- A continuing iteration makes strict progress along a finite execution.
This is operational progress, not the user-supplied termination ranking. -/
theorem IterationExecutes.progress {final : Frame}
    (contains : ∀ pc, exits pc → cuts pc) (outside : ¬ exits s.pc)
    (execution : IterationExecutes next cuts s (.next final)) :
    Relation.TransGen (BeforeExitStep next exits) final s := by
  cases execution with
  | step transition after =>
    exact extend_progress contains after (.single ⟨outside, transition⟩)

end VeriPyAsm.Semantics
