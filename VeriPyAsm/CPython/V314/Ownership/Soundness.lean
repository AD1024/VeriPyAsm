import VeriPyAsm.CPython.V314.Ownership.Certificate
import VeriPyAsm.CPython.V314.Stack.Soundness
import VeriPyAsm.Semantics.Execution

/-! Ownership certificates close all control-flow paths under the reference
protocol. Together with a stack certificate they track every continuing path
of the scalar reference semantics, including the state before a terminal step.
This is a theorem about the modeled protocol, not CPython's C implementation. -/

namespace VeriPyAsm.CPython.V314.Ownership

open Semantics

theorem stackAt_mem {table : Table} {pc : Nat} {refs : Stack}
    (found : stackAt table pc = some refs) : (pc, refs) ∈ table := by
  induction table with
  | nil => simp [stackAt] at found
  | cons row rest ih =>
    rcases row with ⟨offset, values⟩
    by_cases equal : pc = offset
    · subst pc
      have same : values = refs := by simpa [stackAt] using found
      subst refs
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [stackAt, equal] using found))

theorem Certificate.ready {code : Code} (certificate : Certificate code)
    {pc : Nat} {refs : Stack} (known : stackAt certificate.table pc = some refs) :
    ∃ instruction output, fetch code.instructions pc = some instruction ∧
      transfer instruction.op refs = .ok output ∧
      ∀ target ∈ instruction.successors, stackAt certificate.table target = some output := by
  have row := certificate.valid.2.2 _ (stackAt_mem known)
  cases fetched : fetch code.instructions pc with
  | none => simp [RowValid, fetched] at row
  | some instruction =>
    cases effect : transfer instruction.op refs with
    | error _ => simp [RowValid, fetched, effect] at row
    | ok output =>
      exact ⟨instruction, output, rfl, effect, by simpa [RowValid, fetched, effect] using row⟩

/-- The checker rejects hazards at the current instruction, including terminal
instructions; it does not merely describe paths that happen to pass the check. -/
theorem Certificate.no_violation {code : Code} (certificate : Certificate code)
    {pc : Nat} {refs : Stack} {instruction : Instruction}
    (known : stackAt certificate.table pc = some refs)
    (fetched : fetch code.instructions pc = some instruction) (reason : Violation) :
    transfer instruction.op refs ≠ .error reason := by
  obtain ⟨i, output, lookup, effect, _⟩ := certificate.ready known
  have equal := Option.some.inj (fetched.symm.trans lookup)
  subst i
  simp [effect]

/-- A concrete history of stack provenance along selected normal CFG edges. -/
inductive Path (code : Code) : Nat → Stack → Nat → Stack → Prop where
  | refl (pc : Nat) (refs : Stack) : Path code pc refs pc refs
  | step {pc target final : Nat} {refs output finalRefs : Stack} {i : Instruction} :
      fetch code.instructions pc = some i → transfer i.op refs = .ok output →
      target ∈ i.successors → Path code target output final finalRefs →
      Path code pc refs final finalRefs

theorem Certificate.path_preserves {code : Code} (certificate : Certificate code)
    {pc target : Nat} {refs output : Stack} (path : Path code pc refs target output)
    (known : stackAt certificate.table pc = some refs) :
    stackAt certificate.table target = some output := by
  induction path with
  | refl => exact known
  | step fetched effect edge _ ih =>
    obtain ⟨i, after, lookup, transferred, successors⟩ := certificate.ready known
    cases Option.some.inj (fetched.symm.trans lookup)
    cases Except.ok.inj (effect.symm.trans transferred)
    exact ih (successors _ edge)

/-- Every actual continuing execution can be decorated with a safe provenance
history. Stack readiness supplies the link from semantic steps to CFG edges. -/
theorem Certificate.tracks_reaches {code : Code} {capacity : Nat}
    (certificate : Certificate code) (stacks : V314.Stack.Certificate code capacity)
    {s t : Frame} (path : Reaches (referenceStep code) s t) {refs : Stack}
    (shape : stacks.Matches s) (known : stackAt certificate.table s.pc = some refs) :
    ∃ output, Path code s.pc refs t.pc output ∧ stackAt certificate.table t.pc = some output := by
  induction path generalizing refs with
  | refl => exact ⟨refs, .refl _ _, known⟩
  | @step s s' t transition _ ih =>
    obtain ⟨i, output, fetched, effect, successors⟩ := certificate.ready known
    have stackRow := stacks.valid.2.2 _ (V314.Stack.heightAt_mem shape)
    have ready : i.StackReady s.stack.length := by
      simp only [V314.Stack.RowValid, fetched] at stackRow
      exact stackRow.1
    have actual : i.denote s = .next s' := by
      simpa only [referenceStep, fetched] using transition
    have edge := (i.denote_next_stack s s' ready actual).1
    obtain ⟨finalRefs, tracked, finalKnown⟩ :=
      ih (stacks.step_preserves s s' shape transition) (successors _ edge)
    exact ⟨finalRefs, .step fetched effect edge tracked, finalKnown⟩

end VeriPyAsm.CPython.V314.Ownership
