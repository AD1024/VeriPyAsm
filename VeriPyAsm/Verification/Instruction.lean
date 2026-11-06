import VeriPyAsm.Verification.Block

/-! One-step rules for the shallow scalar commands. Preconditions expose stack
shape, local bounds/initialization, and dynamic-operation outcomes explicitly.
The binary rule is shared by arithmetic and comparisons. Exceptional rules keep
the instruction-entry frame, as specified by the machine semantics.

`prepend` composes an instruction with a block, checking actual program lookup
and that the instruction is outside the block's exit set. `to_block` stops after
the instruction at a continuation exit, or immediately at a terminal outcome. -/

namespace VeriPyAsm.Verification

open Semantics

def InstructionCorrect (command : Command) (pre : Frame → Prop)
    (post : Postcondition) : Prop := ∀ s, pre s → post.Accepts (command s)

namespace InstructionCorrect

variable {command : Command} {P P' R : Frame → Prop} {Q Q' : Postcondition}
    {program : Program} {exits : Nat → Prop}

theorem consequence (correct : InstructionCorrect command P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ result, Q.Accepts result → Q'.Accepts result) :
    InstructionCorrect command P' Q' :=
  fun s h => post _ (correct s (pre s h))

/-- Specialize a rule to a symbolic entry frame; the frame may contain arbitrary
Lean parameters. This is not a restriction to concrete test inputs. -/
theorem on_frame (correct : InstructionCorrect command P Q) {initial : Frame}
    (pre : P initial) : InstructionCorrect command (fun s => s = initial) Q := by
  intro s equal
  subst s
  exact correct initial pre

theorem cases (first : InstructionCorrect command P Q)
    (second : InstructionCorrect command P' Q) :
    InstructionCorrect command (fun s => P s ∨ P' s) Q := by
  intro s pre
  rcases pre with pre | pre
  · exact first s pre
  · exact second s pre

theorem prepend_partial (correct : InstructionCorrect command P { Q with continues := R })
    (fetch : ∀ s, P s → program s.pc = some command)
    (outside : ∀ s, P s → ¬ exits s.pc)
    (tail : BlockPartialCorrect (step program) exits R Q) :
    BlockPartialCorrect (step program) exits P Q := by
  intro s pre result execution
  have allowed := correct s pre
  have dispatch : step program s = command s := by simp only [step, fetch s pre]
  cases execution with
  | exit atExit => exact False.elim (outside s pre atExit)
  | @halt _ outcome _ transition =>
    rw [← dispatch, transition] at allowed
    cases outcome <;> exact allowed
  | step _ transition after =>
    rw [← dispatch, transition] at allowed
    exact tail _ allowed _ after

theorem prepend (correct : InstructionCorrect command P { Q with continues := R })
    (fetch : ∀ s, P s → program s.pc = some command)
    (outside : ∀ s, P s → ¬ exits s.pc)
    (tail : BlockTotalCorrect (step program) exits R Q) :
    BlockTotalCorrect (step program) exits P Q := by
  apply BlockTotalCorrect.of_execution
  intro s pre
  have allowed := correct s pre
  have dispatch : step program s = command s := by simp only [step, fetch s pre]
  cases transition : command s with
  | next frame =>
    rw [transition] at allowed
    obtain ⟨result, execution⟩ := tail.terminates frame allowed
    exact ⟨result, .step (outside s pre) (dispatch.trans transition) execution,
      tail.partialCorrect frame allowed result execution⟩
  | halted outcome =>
    rw [transition] at allowed
    refine ⟨.halted outcome, .halt (outside s pre) (dispatch.trans transition), ?_⟩
    cases outcome <;> exact allowed

theorem to_block (correct : InstructionCorrect command P Q)
    (fetch : ∀ s, P s → program s.pc = some command)
    (outside : ∀ s, P s → ¬ exits s.pc)
    (atExit : ∀ s, Q.continues s → exits s.pc) :
    BlockTotalCorrect (step program) exits P Q :=
  correct.prepend fetch outside (.exit atExit (fun _ h => h))

theorem jump (target : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.jump target)
      (fun s => Q.continues { s with pc := target }) Q := fun _ h => h

theorem push (next : Nat) (value : Value) (Q : Postcondition) :
    InstructionCorrect (Command.push next value)
      (fun s => Q.continues { s with pc := next, stack := value :: s.stack }) Q := fun _ h => h

theorem load (checked : Bool) (next index : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.load checked next index)
      (fun s => ∃ value, s.locals[index]? = some (some value) ∧
        Q.continues { s with pc := next, stack := value :: s.stack }) Q := by
  rintro s ⟨value, lookup, post⟩
  simpa only [Command.load, lookup, Command.push, Postcondition.Accepts] using post

theorem load_unbound (next index : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.load true next index)
      (fun s => s.locals[index]? = some none ∧ Q.raises .unboundLocalError s) Q := by
  rintro s ⟨lookup, post⟩
  simpa only [Command.load, lookup, ↓reduceIte, Postcondition.Accepts] using post

theorem store (next index : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.store next index)
      (fun s => index < s.locals.length ∧ ∃ value rest, s.stack = value :: rest ∧
        Q.continues
          { s with pc := next, locals := s.locals.set index (some value), stack := rest }) Q := by
  rintro s ⟨bound, value, rest, stack, post⟩
  simpa only [Command.store, show ¬ index ≥ s.locals.length from Nat.not_le.mpr bound,
    ↓reduceIte, stack, Postcondition.Accepts] using post

theorem binary (next : Nat) (operation : Value → Value → Except PythonException Value)
    (Q : Postcondition) :
    InstructionCorrect (Command.binary next operation)
      (fun s => ∃ left right rest value, s.stack = right :: left :: rest ∧
        operation left right = .ok value ∧
        Q.continues { s with pc := next, stack := value :: rest }) Q := by
  rintro s ⟨left, right, rest, value, stack, result, post⟩
  simpa only [Command.binary, stack, result, Postcondition.Accepts] using post

theorem binary_error (next : Nat) (operation : Value → Value → Except PythonException Value)
    (Q : Postcondition) :
    InstructionCorrect (Command.binary next operation)
      (fun s => ∃ left right rest exception, s.stack = right :: left :: rest ∧
        operation left right = .error exception ∧ Q.raises exception s) Q := by
  rintro s ⟨left, right, rest, exception, stack, result, post⟩
  simpa only [Command.binary, stack, result, Postcondition.Accepts] using post

theorem toBool (next : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.toBool next)
      (fun s => ∃ value rest, s.stack = value :: rest ∧
        Q.continues { s with pc := next, stack := .bool value.truthy :: rest }) Q := by
  rintro s ⟨value, rest, stack, post⟩
  simpa only [Command.toBool, stack, Postcondition.Accepts] using post

/-- Both branch destinations are represented. Only an exact bool can satisfy
the stack premise; truthiness conversion has its own rule. -/
theorem branch (ifTrue ifFalse : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.branch ifTrue ifFalse)
      (fun s => ∃ b rest, s.stack = .bool b :: rest ∧
        Q.continues { s with pc := if b then ifTrue else ifFalse, stack := rest }) Q := by
  rintro s ⟨b, rest, stack, post⟩
  simpa only [Command.branch, stack, Postcondition.Accepts] using post

/-- Return pops an ordinary stack value and exposes it together with the actual
remaining frame. The postcondition can relate both without a new value type. -/
theorem ret (Q : Postcondition) :
    InstructionCorrect Command.ret
      (fun s => ∃ value rest, s.stack = value :: rest ∧
        Q.returned value { s with stack := rest }) Q := by
  rintro s ⟨value, rest, stack, post⟩
  simpa only [Command.ret, stack, Postcondition.Accepts] using post

/-- A real assertion failure must satisfy the exceptional postcondition. In
particular, a contract with `raises := False` cannot discharge this instruction. -/
theorem raiseAssertionError (Q : Postcondition) :
    InstructionCorrect Command.raiseAssertionError
      (fun s => ∃ rest, s.stack = .assertionErrorType :: rest ∧ Q.raises .assertionError s) Q := by
  rintro s ⟨rest, stack, post⟩
  simpa only [Command.raiseAssertionError, stack, Postcondition.Accepts] using post

end InstructionCorrect
end VeriPyAsm.Verification
