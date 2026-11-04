import VeriPyAsm.CPython.V314.Stack.Certificate
import Lean.Elab.Tactic.Omega

/-! The stack certificate implies only stack-shape properties. Python exceptions
and faults concerning locals or value tags remain possible. The worklist analyzer
is not part of these proofs. -/

namespace VeriPyAsm.CPython.V314

open Semantics

private def StackResult (i : Instruction) (height : Nat) : StepResult → Prop
  | .next frame => frame.pc ∈ i.successors ∧ frame.stack.length = i.outputHeight height
  | .halted (.returned _ frame) => frame.stack = []
  | .halted (.fault .stackUnderflow _) => False
  | _ => True

private theorem denote_stack_result (i : Instruction) (s : Frame)
    (ready : i.StackReady s.stack.length) : StackResult i s.stack.length (i.denote s) := by
  cases i with
  | mk offset next opcode arg op =>
    cases op <;>
      simp_all only [Instruction.StackReady, Op.pops, Instruction.denote,
        Command.jump, Command.push, Command.load, Command.store,
        Command.loadPair, Command.storeLoad, Command.storePair,
        Command.binary, Command.toBool, Command.branch, Command.ret]
    all_goals
      repeat first
        | (solve | simp_all [StackResult, Instruction.outputHeight, Op.pops,
            Op.pushes, Instruction.successors])
        | split
        | omega
    all_goals
      cases hstack : s.stack with
      | nil => simp_all
      | cons a rest =>
        cases rest with
        | nil => simp_all
        | cons b tail => simp_all

theorem Instruction.denote_next_stack (i : Instruction) (s t : Frame)
    (ready : i.StackReady s.stack.length) (step : i.denote s = .next t) :
    t.pc ∈ i.successors ∧ t.stack.length = i.outputHeight s.stack.length := by
  simpa only [step, StackResult] using denote_stack_result i s ready

theorem Instruction.denote_no_underflow (i : Instruction) (s : Frame)
    (ready : i.StackReady s.stack.length) (failureFrame : Frame) :
    i.denote s ≠ .halted (.fault .stackUnderflow failureFrame) := by
  intro step
  simpa only [step, StackResult] using denote_stack_result i s ready

theorem Instruction.denote_return_stack (i : Instruction) (s t : Frame) (value : Value)
    (ready : i.StackReady s.stack.length) (step : i.denote s = .halted (.returned value t)) :
    t.stack = [] := by
  simpa only [step, StackResult] using denote_stack_result i s ready

namespace Stack

theorem heightAt_mem {heights : Heights} {pc height : Nat}
    (found : heightAt heights pc = some height) : (pc, height) ∈ heights := by
  induction heights with
  | nil => simp [heightAt] at found
  | cons row rest ih =>
    rcases row with ⟨offset, rowHeight⟩
    by_cases equal : pc = offset
    · subst pc
      have same : rowHeight = height := by simpa [heightAt] using found
      subst height
      exact List.mem_cons_self
    · have tail : heightAt rest pc = some height := by
        simpa [heightAt, equal] using found
      exact List.mem_cons_of_mem _ (ih tail)

/-- A concrete frame has the height assigned to its PC by this certificate. -/
def Certificate.Matches {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (frame : Frame) : Prop :=
  heightAt certificate.heights frame.pc = some frame.stack.length

theorem Certificate.entry_matches {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (locals : List (Option Value)) :
    certificate.Matches { locals } := certificate.valid.1

private theorem Certificate.valid_row {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (s : Frame) (shape : certificate.Matches s) :
    RowValid code capacity certificate.heights (s.pc, s.stack.length) :=
  certificate.valid.2.2 _ (heightAt_mem shape)

theorem Certificate.frame_bound {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (s : Frame) (shape : certificate.Matches s) :
    s.stack.length ≤ capacity := by
  have row := certificate.valid_row s shape
  unfold RowValid at row
  split at row
  · contradiction
  · exact row.2.1

theorem Certificate.step_preserves {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (s t : Frame) (shape : certificate.Matches s)
    (step : referenceStep code s = .next t) : certificate.Matches t := by
  have row := certificate.valid_row s shape
  unfold referenceStep at step
  unfold RowValid at row
  cases fetched : fetch code.instructions s.pc with
  | none => simp only [fetched] at row
  | some instruction =>
    simp only [fetched] at step row
    have shape := instruction.denote_next_stack s t row.1 step
    unfold Matches
    rw [shape.2]
    exact row.2.2.2 t.pc shape.1

theorem Certificate.step_no_underflow {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (s : Frame) (shape : certificate.Matches s)
    (failureFrame : Frame) :
    referenceStep code s ≠ .halted (.fault .stackUnderflow failureFrame) := by
  have row := certificate.valid_row s shape
  unfold referenceStep
  unfold RowValid at row
  cases fetched : fetch code.instructions s.pc with
  | none => simp only [fetched] at row
  | some instruction =>
    simp only [fetched] at row
    exact instruction.denote_no_underflow s row.1 failureFrame

theorem Certificate.step_return_stack {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (s t : Frame) (value : Value)
    (shape : certificate.Matches s) (step : referenceStep code s = .halted (.returned value t)) :
    t.stack = [] := by
  have row := certificate.valid_row s shape
  unfold referenceStep at step
  unfold RowValid at row
  cases fetched : fetch code.instructions s.pc with
  | none => simp only [fetched] at row
  | some instruction =>
    simp only [fetched] at step row
    exact instruction.denote_return_stack s t value row.1 step

/-- Every continuation reached after any finite number of normal steps retains
the certified height. No assumption that the program terminates is needed. -/
theorem Certificate.run_exhausted_matches {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (fuel : Nat) (s t : Frame)
    (shape : certificate.Matches s)
    (execution : run (referenceStep code) fuel s = .exhausted t) :
    certificate.Matches t := by
  induction fuel generalizing s with
  | zero =>
    simp only [run, RunResult.exhausted.injEq] at execution
    subst t
    exact shape
  | succ fuel ih =>
    cases next : referenceStep code s with
    | halted outcome => simp [run, next] at execution
    | next s' =>
      simp only [run, next] at execution
      exact ih s' (certificate.step_preserves s s' shape next) execution

theorem Certificate.run_exhausted_bound {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (fuel : Nat) (s t : Frame)
    (shape : certificate.Matches s)
    (execution : run (referenceStep code) fuel s = .exhausted t) :
    t.stack.length ≤ capacity :=
  certificate.frame_bound t (certificate.run_exhausted_matches fuel s t shape execution)

theorem Certificate.run_no_underflow {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (fuel : Nat) (s : Frame)
    (shape : certificate.Matches s) (failureFrame : Frame) :
    run (referenceStep code) fuel s ≠ .halted (.fault .stackUnderflow failureFrame) := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    intro execution
    cases next : referenceStep code s with
    | next s' =>
      simp only [run, next] at execution
      exact ih s' (certificate.step_preserves s s' shape next) execution
    | halted outcome =>
      have same : outcome = .fault .stackUnderflow failureFrame := by
        simpa only [run, next, RunResult.halted.injEq] using execution
      exact certificate.step_no_underflow s shape failureFrame
        (next.trans (congrArg StepResult.halted same))

theorem Certificate.run_return_stack {code : Code} {capacity : Nat}
    (certificate : Certificate code capacity) (fuel : Nat) (s t : Frame) (value : Value)
    (shape : certificate.Matches s)
    (execution : run (referenceStep code) fuel s = .halted (.returned value t)) :
    t.stack = [] := by
  induction fuel generalizing s with
  | zero => simp [run] at execution
  | succ fuel ih =>
    cases next : referenceStep code s with
    | next s' =>
      simp only [run, next] at execution
      exact ih s' (certificate.step_preserves s s' shape next) execution
    | halted outcome =>
      have same : outcome = .returned value t := by
        simpa only [run, next, RunResult.halted.injEq] using execution
      exact certificate.step_return_stack s t value shape
        (next.trans (congrArg StepResult.halted same))

end Stack

end VeriPyAsm.CPython.V314
