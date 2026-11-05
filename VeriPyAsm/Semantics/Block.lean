import VeriPyAsm.Semantics.Execution

/-! Finite execution up to the first designated bytecode location or a halt.
An exit location is observed before its instruction executes. `.next` exposes
that continuation frame; `.halted` retains the machine's return/exception/fault.
This relation adds observation boundaries, not new machine transitions. -/

namespace VeriPyAsm.Semantics

inductive BlockExecutes (next : Frame → StepResult) (exits : Nat → Prop) :
    Frame → StepResult → Prop where
  | exit {s : Frame} : exits s.pc → BlockExecutes next exits s (.next s)
  | halt {s : Frame} {outcome : Halt} :
      ¬ exits s.pc → next s = .halted outcome →
      BlockExecutes next exits s (.halted outcome)
  | step {s s' : Frame} {result : StepResult} :
      ¬ exits s.pc → next s = .next s' → BlockExecutes next exits s' result →
      BlockExecutes next exits s result

variable {next : Frame → StepResult} {exits cuts : Nat → Prop}
    {s t : Frame} {result : StepResult} {outcome : Halt}

theorem BlockExecutes.sound (execution : BlockExecutes next exits s result) :
    match result with
    | .next t => Reaches next s t ∧ exits t.pc
    | .halted outcome => Executes next s outcome := by
  induction execution with
  | exit atExit => exact ⟨.refl _, atExit⟩
  | halt _ transition => exact .halt transition
  | @step s s' result _ transition _ ih =>
    cases result with
    | next t => exact ⟨.step transition ih.1, ih.2⟩
    | halted outcome => exact .step transition ih

theorem BlockExecutes.continues (execution : BlockExecutes next exits s (.next t)) :
    Reaches next s t := execution.sound.1

theorem BlockExecutes.exit_at (execution : BlockExecutes next exits s (.next t)) :
    exits t.pc := execution.sound.2

theorem BlockExecutes.halts (execution : BlockExecutes next exits s (.halted outcome)) :
    Executes next s outcome := execution.sound

theorem BlockExecutes.of_execution (execution : Executes next s outcome) :
    BlockExecutes next (fun _ => False) s (.halted outcome) := by
  induction execution with
  | halt transition => exact .halt (fun h => h) transition
  | step transition _ ih => exact .step (fun h => h) transition ih

theorem BlockExecutes.deterministic {other : StepResult}
    (first : BlockExecutes next exits s result)
    (second : BlockExecutes next exits s other) : result = other := by
  induction first with
  | exit atExit =>
    cases second with
    | exit => rfl
    | halt outside _ => exact False.elim (outside atExit)
    | step outside _ _ => exact False.elim (outside atExit)
  | halt outside transition =>
    cases second with
    | exit atExit => exact False.elim (outside atExit)
    | halt _ transition' => exact transition.symm.trans transition'
    | step _ transition' _ => cases transition.symm.trans transition'
  | step outside transition _ ih =>
    cases second with
    | exit atExit => exact False.elim (outside atExit)
    | halt _ transition' => cases transition.symm.trans transition'
    | step _ transition' tail =>
      have equal := StepResult.next.inj (transition.symm.trans transition')
      cases equal
      exact ih tail

/-- Compose at a cutpoint. Every final exit must also stop the prefix, so the
prefix cannot silently execute past an earlier final exit. Terminal outcomes
bypass the suffix; they cannot resume as continuations. -/
theorem BlockExecutes.append
    (contains : ∀ pc, exits pc → cuts pc)
    (first : BlockExecutes next cuts s result) {final : StepResult}
    (suffix : match result with
      | .next middle => BlockExecutes next exits middle final
      | .halted outcome => final = .halted outcome) :
    BlockExecutes next exits s final := by
  induction first with
  | exit => exact suffix
  | halt outside transition =>
    cases suffix
    exact .halt (fun h => outside (contains _ h)) transition
  | @step s s' result outside transition _ ih =>
    cases result <;>
      exact .step (fun h => outside (contains _ h)) transition (ih suffix)

/-- Split a finite execution at its first cutpoint, or at its terminal outcome
if no cutpoint is reached. This also supports partial-correctness sequencing:
the prefix need not terminate on executions that diverge. -/
theorem BlockExecutes.split
    (contains : ∀ pc, exits pc → cuts pc)
    (execution : BlockExecutes next exits s result) :
    ∃ middle, BlockExecutes next cuts s middle ∧
      match middle with
      | .next frame => BlockExecutes next exits frame result
      | .halted outcome => result = .halted outcome := by
  classical
  induction execution with
  | exit atExit => exact ⟨_, .exit (contains _ atExit), .exit atExit⟩
  | @halt s outcome outside transition =>
    by_cases atCut : cuts s.pc
    · exact ⟨_, .exit atCut, .halt outside transition⟩
    · exact ⟨_, .halt atCut transition, rfl⟩
  | @step s s' result outside transition tail ih =>
    by_cases atCut : cuts s.pc
    · exact ⟨_, .exit atCut, .step outside transition tail⟩
    · obtain ⟨middle, before, suffix⟩ := ih
      exact ⟨middle, .step atCut transition before, suffix⟩

end VeriPyAsm.Semantics
