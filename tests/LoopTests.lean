import VeriPyAsm.Verification.Loop

/-! Loop regressions distinguish real iterations from zero-step exits, strict
ranking from non-increase, and termination of a body from header preservation. -/

namespace VeriPyAsm.Tests.Loop

open Semantics Verification

private def countdown : Frame → StepResult := fun s => .next { s with pc := s.pc - 1 }

/-- The final PC is a continuation, not a return. The same machine would loop
forever at zero if that final exit were executed. -/
theorem countdown_total :
    BlockTotalCorrect countdown (fun pc => pc = 0) (fun s => 0 < s.pc)
      { continues := fun s => s.pc = 0 } := by
  apply BlockTotalCorrect.loop (cuts := fun _ => True) Frame.pc
    (fun _ _ => trivial) (fun s positive zero => by omega)
  intro initial positive
  apply IterationTotalCorrect.of_execution
  intro s equal
  subst s
  refine ⟨.next { initial with pc := initial.pc - 1 }, .step rfl (.exit trivial), ?_⟩
  by_cases zero : initial.pc - 1 = 0
  · exact Or.inl ⟨zero, zero⟩
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩

private def stationary : Frame → StepResult := fun s => .next s

theorem stationary_partial :
    BlockPartialCorrect stationary (fun _ => False) (fun _ => True) {} := by
  apply BlockPartialCorrect.loop (cuts := fun _ => True)
    (fun _ h => False.elim h) (fun _ _ h => h)
  have body : IterationTotalCorrect stationary (fun _ => True) (fun _ => True)
      { continues := fun _ => (False ∧ False) ∨ True } := by
    apply IterationTotalCorrect.of_execution
    intro s _
    exact ⟨.next s, .step rfl (.exit trivial), Or.inr trivial⟩
  exact body.partialCorrect

theorem unchanged_rank_rejected (rank : Frame → Nat) :
    ¬ IterationPartialCorrect stationary (fun _ => True) (fun s => s = {})
      { continues := fun s => rank s < rank {} } := by
  intro correct
  have smaller := correct {} rfl (.next {}) (.step rfl (.exit trivial))
  exact Nat.lt_irrefl _ smaller

private def invalid : Frame → StepResult := fun s => .halted (.fault .stackUnderflow s)

-- A zero-step exit is valid for a block, even when its next instruction faults.
example : BlockTotalCorrect invalid (fun _ => True) (fun _ => True)
    { continues := fun _ => True } := .exit (fun _ _ => trivial) (fun _ _ => trivial)

-- It is not a valid loop iteration: the first instruction must actually execute.
theorem zero_step_cannot_hide_fault :
    ¬ IterationPartialCorrect invalid (fun _ => True) (fun _ => True)
      { continues := fun _ => True, returned := fun _ _ => True, raises := fun _ _ => True } := by
  intro correct
  exact correct {} trivial _ (.halt rfl)

private def stranded : Frame → StepResult := fun s => .next { s with pc := 1 }

private theorem stranded_no_exit {s : Frame} {result : StepResult}
    (execution : BlockExecutes stranded (fun pc => pc = 0) s result) : s.pc = 1 → False := by
  induction execution with
  | exit atExit => intro atOne; omega
  | halt _ impossible => cases impossible
  | step _ transition _ ih =>
    intro _
    apply ih
    cases transition
    rfl

private theorem stranded_no_iteration {s : Frame} {result : StepResult}
    (execution : IterationExecutes stranded (fun pc => pc = 0) s result) : False := by
  cases execution with
  | halt impossible => cases impossible
  | step transition after =>
    apply stranded_no_exit after
    cases transition
    rfl

theorem divergent_body_partial :
    IterationPartialCorrect stranded (fun pc => pc = 0) (fun s => s.pc = 0)
      { continues := fun s => s.pc = 0 } :=
  fun _ _ _ execution => False.elim (stranded_no_iteration execution)

theorem divergent_body_not_total :
    ¬ IterationTotalCorrect stranded (fun pc => pc = 0) (fun s => s.pc = 0)
      { continues := fun s => s.pc = 0 } := by
  intro correct
  obtain ⟨_, execution⟩ := correct.terminates {} rfl
  exact stranded_no_iteration execution

private theorem terminal_iteration (outcome : Halt) (post : Postcondition)
    (accepted : post.Accepts (.halted outcome)) :
    BlockTotalCorrect (fun _ => .halted outcome) (fun _ => False) (fun _ => True) post := by
  apply BlockTotalCorrect.loop (cuts := fun _ => True) (fun _ => 0)
    (fun _ h => False.elim h) (fun _ _ h => h)
  intro initial _
  apply IterationTotalCorrect.of_execution
  intro s _
  refine ⟨.halted outcome, .halt rfl, ?_⟩
  cases outcome <;> exact accepted

-- Terminal exits do not need a decrease; they must satisfy the stated outcome.
example (value : Value) (rest : List Value) :
    BlockTotalCorrect (fun _ => .halted (.returned value { stack := rest }))
      (fun _ => False) (fun _ => True)
      { returned := fun result final => result = value ∧ final.stack = rest } :=
  terminal_iteration _ _ ⟨rfl, rfl⟩

example : BlockTotalCorrect (fun _ => .halted (.raised .typeError {}))
    (fun _ => False) (fun _ => True) { raises := fun exception _ => exception = .typeError } :=
  terminal_iteration _ _ rfl

#print axioms IterationExecutes.append
#print axioms IterationExecutes.progress
#print axioms BlockPartialCorrect.loop
#print axioms BlockTotalCorrect.loop_wellFounded
#print axioms BlockTotalCorrect.loop
#print axioms countdown_total
#print axioms stationary_partial
#print axioms unchanged_rank_rejected
#print axioms zero_step_cannot_hide_fault
#print axioms divergent_body_not_total

end VeriPyAsm.Tests.Loop
