import VeriPyAsm.Verification.Iteration

/-! Cutpoint loop rules. An iteration must execute at least one instruction.
Partial correctness needs invariant preservation on every back edge. Total
correctness also needs termination of each iteration and a strict decrease in
a well-founded relation; merely preserving or not increasing a rank is not enough.
All final exits must be cutpoints, and invariant states must be outside them. -/

namespace VeriPyAsm.Verification

open Semantics

variable {next : Frame → StepResult} {cuts exits : Nat → Prop}
    {I : Frame → Prop} {Q : Postcondition}

/-- The iteration either reaches an allowed final continuation or reestablishes
I. Returns and exceptions satisfy Q directly. Divergent iterations are allowed. -/
theorem BlockPartialCorrect.loop
    (contains : ∀ pc, exits pc → cuts pc)
    (outside : ∀ s, I s → ¬ exits s.pc)
    (body : IterationPartialCorrect next cuts I
      { Q with continues := fun s => (exits s.pc ∧ Q.continues s) ∨ I s }) :
    BlockPartialCorrect next exits I Q := by
  have sound : ∀ s, Acc (Relation.TransGen (BeforeExitStep next exits)) s →
      I s → ∀ result, BlockExecutes next exits s result → Q.Accepts result := by
    intro s accessible
    induction accessible with
    | intro s _ ih =>
      intro invariant result execution
      obtain ⟨middle, iteration, after⟩ :=
        execution.split_iteration contains (outside s invariant)
      have allowed := body s invariant middle iteration
      cases middle with
      | next frame =>
        rcases allowed with ⟨atExit, post⟩ | preserved
        · have equal := after.deterministic (.exit atExit)
          cases equal
          exact post
        · exact ih frame (iteration.progress contains (outside s invariant))
            preserved result after
      | halted outcome =>
        cases after
        cases outcome <;> exact allowed
  intro s invariant result execution
  exact sound s execution.accessible.transGen invariant result execution

/-- The relation is oriented `decreases new old`. It can express lexicographic
or other well-founded rankings, without requiring a scalar numeric measure. -/
theorem BlockTotalCorrect.loop_wellFounded
    (decreases : Frame → Frame → Prop) (wellFounded : WellFounded decreases)
    (contains : ∀ pc, exits pc → cuts pc)
    (outside : ∀ s, I s → ¬ exits s.pc)
    (body : ∀ initial, I initial →
      IterationTotalCorrect next cuts (fun s => s = initial)
        { Q with continues := fun s =>
            (exits s.pc ∧ Q.continues s) ∨ (I s ∧ decreases s initial) }) :
    BlockTotalCorrect next exits I Q := by
  apply BlockTotalCorrect.of_execution
  intro initial
  induction initial using wellFounded.induction with
  | h initial ih =>
    intro invariant
    have correct := body initial invariant
    obtain ⟨middle, iteration⟩ := correct.terminates initial rfl
    have allowed := correct.partialCorrect initial rfl middle iteration
    cases middle with
    | next frame =>
      rcases allowed with ⟨atExit, post⟩ | ⟨preserved, smaller⟩
      · exact ⟨.next frame, iteration.append contains (outside initial invariant) (.exit atExit),
          post⟩
      · obtain ⟨result, execution, post⟩ := ih frame smaller preserved
        exact ⟨result, iteration.append contains (outside initial invariant) execution, post⟩
    | halted outcome =>
      refine ⟨.halted outcome, iteration.append contains (outside initial invariant) rfl, ?_⟩
      cases outcome <;> exact allowed

/-- A natural-number ranking is the common case of the well-founded rule.
The rank is compared only between invariant states, not at every instruction. -/
theorem BlockTotalCorrect.loop (rank : Frame → Nat)
    (contains : ∀ pc, exits pc → cuts pc)
    (outside : ∀ s, I s → ¬ exits s.pc)
    (body : ∀ initial, I initial →
      IterationTotalCorrect next cuts (fun s => s = initial)
        { Q with continues := fun s =>
            (exits s.pc ∧ Q.continues s) ∨ (I s ∧ rank s < rank initial) }) :
    BlockTotalCorrect next exits I Q :=
  .loop_wellFounded (fun new old => rank new < rank old) (measure rank).wf
    contains outside body

end VeriPyAsm.Verification
