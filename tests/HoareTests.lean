import VeriPyAsm.Verification.Hoare
import VeriPyAsm.Examples.Add1

/-! The Hoare syntax is an exact presentation of the existing correctness
judgments. These checks cover parsing, captured logical inputs, final-frame
observations, and the distinction between normal return and failure/divergence. -/

namespace VeriPyAsm.Tests.Hoare

open Semantics Verification Examples
open scoped VeriPyAsm.Verification.Hoare

example (P Q : Frame → Prop) (S : Program) :
    ({ P } S { Q }) =
      PartialCorrect (step S) (Contract.ofFramePredicates P Q) := rfl

example (P Q : Frame → Prop) (S : Program) :
    ({{ P }} S {{ Q }}) =
      TotalCorrect (step S) (Contract.ofFramePredicates P Q) := rfl

-- The final brace does not consume a following implication or conjunction.
example (P Q : Frame → Prop) (S : Program) :
    {{ P }} S {{ Q }} → { P } S { Q } := fun correct => correct.partialCorrect

example (P Q : Frame → Prop) (S : Program) :
    {{ P }} S {{ Q }} → { P } S { Q } ∧ True :=
  fun correct => ⟨correct.partialCorrect, trivial⟩

example (P Q : Frame → Prop) (S : Program) :
    ({ P } S { Q }) ∧ True → { P } S { Q } := fun both => both.1

-- Ordinary record construction and updates retain their usual syntax in scope.
example : ({ pc := 7, stack := [.int 3] } : Frame).pc = 7 := rfl
example (initial : Frame) : ({ initial with stack := [] } : Frame).stack = [] := rfl

private def returnProgram : Program := fun _ => some Command.ret

/-- The returned value has been popped: Q sees the remaining operand stack. -/
theorem return_stack (value : Value) (rest : List Value) :
    {{ fun initial => initial.stack = value :: rest }} returnProgram
    {{ fun final => final.stack = rest }} := by
  apply TotalCorrect.of_run
  intro _ initial pre
  change initial.stack = value :: rest at pre
  refine ⟨1, .returned value { initial with stack := rest }, ?_, rfl⟩
  simp [run, step, returnProgram, Command.ret, pre]

-- A parenthesized application can supply S, and nested records can occur in P.
-- Outer inputs remain bound across both predicate lambdas.
theorem add1_notation (n : Int) :
    {{ fun initial => initial = { locals := [some (.int n)] } }}
      (id add1Admitted.translation.program)
    {{ fun final => final.locals = [some (.int n)] ∧ final.stack = [] }} := by
  apply TotalCorrect.of_execution
  intro _ initial pre
  change initial = { locals := [some (.int n)] } at pre
  subst initial
  obtain ⟨outcome, execution⟩ := add1_total.terminates n
    { locals := [some (.int n)] } rfl
  refine ⟨outcome, execution, ?_⟩
  have allowed := add1_total.partialCorrect n _ rfl outcome execution
  cases outcome with
  | returned value final => exact ⟨allowed.2.1, allowed.2.2⟩
  | raised exception final => exact False.elim allowed
  | fault reason final => exact False.elim allowed

private def loopProgram : Program := fun _ => some (fun initial => .next initial)

private theorem loop_no_execution {initial : Frame} {outcome : Halt}
    (execution : Executes (step loopProgram) initial outcome) : False := by
  induction execution with
  | halt transition => cases transition
  | step _ _ ih => exact ih

theorem loop_partial : { fun _ => True } loopProgram { fun _ => False } := by
  intro _ _ _ _ execution
  exact False.elim (loop_no_execution execution)

theorem loop_not_total : ¬ ({{ fun _ => True }} loopProgram {{ fun _ => False }}) := by
  intro correct
  obtain ⟨_, execution⟩ := correct.terminates () {} trivial
  exact loop_no_execution execution

private def invalidProgram : Program := fun _ => none

-- A permissive postcondition cannot authorize a VM fault.
theorem fault_rejected : ¬ ({ fun _ => True } invalidProgram { fun _ => True }) := by
  intro correct
  exact correct.no_fault (ghost := ()) (initial := {}) trivial (.invalidPC 0) {}
    (.halt rfl)

private def exceptionProgram : Program := fun _ =>
  some (fun initial => .halted (.raised .typeError initial))

-- The simple two-predicate syntax requires normal return. Explicitly allowed
-- exceptions remain expressible through the full Contract interface.
theorem exception_rejected :
    ¬ ({ fun _ => True } exceptionProgram { fun _ => True }) := by
  intro correct
  exact correct () {} trivial (.raised .typeError {}) (.halt rfl)

#print axioms return_stack
#print axioms add1_notation
#print axioms loop_partial
#print axioms loop_not_total
#print axioms fault_rejected
#print axioms exception_rejected

end VeriPyAsm.Tests.Hoare
