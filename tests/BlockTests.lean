import VeriPyAsm.Verification.Block

/-! Boundaries that a compositional block logic must preserve: first exit,
terminal exits that bypass the suffix, faults, and divergent partial proofs. -/

namespace VeriPyAsm.Tests.Block

open Semantics Verification

private def pushJump (value : Value) : Program := fun pc =>
  if pc = 0 then some (Command.push 1 value)
  else if pc = 1 then some (Command.jump 2)
  else none

/-- The final location has no instruction. Reaching it is a valid block exit;
executing it would fault. Both sequence boundaries retain the pushed value. -/
theorem two_blocks (value : Value) :
    BlockTotalCorrect (step (pushJump value)) (fun pc => pc = 2)
      (fun s => s = {}) { continues := fun s => s = { pc := 2, stack := [value] } } := by
  let middle : Frame → Prop := fun s => s = { pc := 1, stack := [value] }
  let post : Postcondition := { continues := fun s => s = { pc := 2, stack := [value] } }
  have first : BlockTotalCorrect (step (pushJump value)) (fun pc => pc = 1 ∨ pc = 2)
      (fun s => s = {}) { post with continues := middle } := by
    apply BlockTotalCorrect.of_execution
    rintro s rfl
    exact ⟨.next { pc := 1, stack := [value] },
      .step (by decide) rfl (.exit (Or.inl rfl)), rfl⟩
  have second : BlockTotalCorrect (step (pushJump value)) (fun pc => pc = 2) middle post := by
    apply BlockTotalCorrect.of_execution
    rintro s rfl
    exact ⟨.next { pc := 2, stack := [value] },
      .step (by simp) rfl (.exit rfl), rfl⟩
  exact first.seq second (fun _ h => Or.inr h)

example (value : Value) :
    BlockPartialCorrect (step (pushJump value)) (fun pc => pc = 2)
      (fun s => s = {}) { continues := fun s => s.stack = [value] } := by
  apply (two_blocks value).partialCorrect.consequence (fun _ h => h)
  intro result allowed
  cases result with
  | next s => cases allowed; rfl
  | halted outcome => cases outcome <;> exact allowed

theorem cannot_skip_first_exit (value : Value) :
    ¬ BlockPartialCorrect (step (pushJump value)) (fun pc => pc = 0 ∨ pc = 2)
      (fun s => s = {}) { continues := fun s => s.pc = 2 } := by
  intro correct
  have impossible := correct {} rfl (.next {}) (.exit (Or.inl rfl))
  exact (by decide : ¬ ((0 : Nat) = 2)) impossible

private def returnProgram : Program := fun _ => some Command.ret

theorem entry_exit (value : Value) :
    BlockTotalCorrect (step returnProgram) (fun pc => pc = 0)
      (fun s => s = { stack := [value] })
      { continues := fun s => s.stack = [value] } :=
  .exit (by rintro s rfl; rfl) (by rintro s rfl; rfl)

theorem exit_precedes_return (value : Value) :
    ¬ BlockExecutes (step returnProgram) (fun pc => pc = 0)
      { stack := [value] } (.halted (.returned value {})) := by
  intro execution
  have impossible := execution.deterministic (.exit rfl)
  cases impossible

/-- An early return skips a suffix whose precondition is False. The return is
still an ordinary stack value, and its relation to the remaining stack survives. -/
theorem early_return (value : Value) (rest : List Value) :
    TotalCorrect (step returnProgram)
      (({ returned := fun returned final => returned = value ∧ final.stack = rest } :
        Postcondition).toContract (fun s => s = { stack := value :: rest })) := by
  let post : Postcondition :=
    { returned := fun returned final => returned = value ∧ final.stack = rest }
  have first : BlockTotalCorrect (step returnProgram) (fun pc => pc = 1)
      (fun s => s = { stack := value :: rest }) { post with continues := fun _ => False } := by
    apply BlockTotalCorrect.of_execution
    rintro s rfl
    exact ⟨.halted (.returned value { stack := rest }), .halt (by simp) rfl, rfl, rfl⟩
  have suffix : BlockTotalCorrect (step returnProgram) (fun _ => False) (fun _ => False) post :=
    .of_execution (fun _ impossible => False.elim impossible)
  exact (first.seq suffix (fun _ impossible => False.elim impossible)).to_totalCorrect

private def exceptional : Frame → StepResult := fun s => .halted (.raised .typeError s)

theorem early_exception :
    BlockTotalCorrect exceptional (fun _ => False) (fun _ => True)
      { raises := fun exception _ => exception = .typeError } := by
  let post : Postcondition := { raises := fun exception _ => exception = .typeError }
  have first : BlockTotalCorrect exceptional (fun _ => False) (fun _ => True)
      { post with continues := fun _ => False } := by
    apply BlockTotalCorrect.of_execution
    intro s _
    exact ⟨_, .halt (fun h => h) rfl, rfl⟩
  have suffix : BlockTotalCorrect exceptional (fun _ => False) (fun _ => False) post :=
    .of_execution (fun _ impossible => False.elim impossible)
  exact first.seq suffix (fun _ h => h)

private def invalid : Frame → StepResult := fun s => .halted (.fault .stackUnderflow s)

theorem faults_forbidden :
    ¬ BlockPartialCorrect invalid (fun _ => False) (fun _ => True)
      { continues := fun _ => True, returned := fun _ _ => True, raises := fun _ _ => True } := by
  intro correct
  exact correct {} trivial _ (.halt (fun h => h) rfl)

private def selfLoop : Frame → StepResult := fun s => .next s

private theorem loop_no_exit {s : Frame} {result : StepResult}
    (execution : BlockExecutes selfLoop (fun _ => False) s result) : False := by
  induction execution with
  | exit impossible => exact impossible
  | halt _ impossible => cases impossible
  | step _ _ _ ih => exact ih

theorem divergent_partial :
    BlockPartialCorrect selfLoop (fun _ => False) (fun _ => True) {} :=
  fun _ _ _ execution => False.elim (loop_no_exit execution)

theorem divergent_not_total :
    ¬ BlockTotalCorrect selfLoop (fun _ => False) (fun _ => True) {} := by
  intro correct
  obtain ⟨_, execution⟩ := correct.terminates {} trivial
  exact loop_no_exit execution

-- Partial sequencing does not require termination of its prefix.
example : BlockPartialCorrect selfLoop (fun _ => False) (fun _ => True) {} :=
  divergent_partial.seq
    (show BlockPartialCorrect selfLoop (fun _ => False) (fun _ => False) {} from
      fun _ impossible => False.elim impossible)
    (fun _ h => h)

#print axioms BlockExecutes.sound
#print axioms BlockExecutes.deterministic
#print axioms BlockExecutes.append
#print axioms BlockPartialCorrect.seq
#print axioms BlockTotalCorrect.seq
#print axioms BlockPartialCorrect.to_partialCorrect
#print axioms BlockTotalCorrect.to_totalCorrect
#print axioms two_blocks
#print axioms early_return
#print axioms early_exception
#print axioms faults_forbidden
#print axioms divergent_not_total

end VeriPyAsm.Tests.Block
