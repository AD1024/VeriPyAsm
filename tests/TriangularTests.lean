import VeriPyAsm.Examples.Triangular

/-! Universal loop-contract checks, its necessary input boundary, and a freshly
stack-admitted bytecode mutation that violates the functional specification. -/

namespace VeriPyAsm.Tests.Triangular

open Semantics Verification Examples CPython.V314
open scoped VeriPyAsm.Verification.Hoare

/-- Termination supplies a fuel witness for every natural input, not a chosen
finite test set or an assumed bound on the loop. -/
theorem all_natural_inputs (n : Nat) :
    ∃ fuel result final,
      run (step triangular.translation.program) fuel { locals := [some (.int n), none] } =
        .halted (.returned (.int result) final) ∧
      2 * result = (n : Int) * (n + 1) ∧ final.stack = [] := by
  obtain ⟨fuel, outcome, execution, allowed⟩ :=
    (triangular_total n).exists_run (ghost := ()) ⟨by omega, rfl⟩
  cases outcome with
  | returned value final =>
    obtain ⟨result, equal, equation, _, stack⟩ := allowed
    subst value
    exact ⟨fuel, result, final, execution, equation, stack⟩
  | raised _ _ => exact False.elim allowed
  | fault _ _ => exact False.elim allowed

theorem zero_result {fuel : Nat} {value : Value} {final : Frame}
    (execution : run (step triangular.translation.program) fuel
      { locals := [some (.int 0), none] } = .halted (.returned value final)) :
    value = .int 0 ∧ final.locals = [some (.int 0), some (.int 0)] ∧ final.stack = [] := by
  obtain ⟨result, equal, equation, locals, stack⟩ :=
    (triangular_total 0).partialCorrect.run_halted (ghost := ()) ⟨by omega, rfl⟩ execution
  have zero : result = 0 := by omega
  subst result
  exact ⟨equal, locals, stack⟩

theorem nonnegative_precondition_needed :
    ¬ ({ fun initial => initial = { locals := [some (.int (-2)), none] } }
      triangular.translation.program
    { returns fun value _ => ∃ result : Int, value = .int result ∧
        2 * result = (-2 : Int) * (-2 + 1) }) := by
  intro correct
  have allowed := correct.run_halted (ghost := ()) rfl
    (show run (step triangular.translation.program) 20
      { locals := [some (.int (-2)), none] } =
        .halted (.returned (.int 0) { pc := 60, locals := [some (.int (-2)), some (.int 0)] })
      from by decide +kernel)
  obtain ⟨result, tag, equation⟩ := allowed
  have zero := Value.int.inj tag
  omega

/-- Change the body's BINARY_OP + to subtraction; layout and stack effects stay
valid, so stack admission alone cannot establish the arithmetic contract. -/
private def changedArtifact : Artifact :=
  { triangularArtifact with code := triangularArtifact.code.set 23 10 }

private def changed : StackAdmitted changedArtifact := admit_bytecode% changedArtifact

theorem changed_artifact_rejected :
    ¬ ArtifactPartialCorrect changedArtifact triangularContract := by
  intro artifactCorrect
  have correct := changed.translation.artifact_partial_iff.mp artifactCorrect
  have allowed := correct.run_halted (ghost := 1) ⟨by decide, rfl⟩
    (show run (step changed.translation.program) 50 { locals := [some (.int 1), none] } =
      .halted (.returned (.int (-1)) { pc := 60, locals := [some (.int 0), some (.int (-1))] })
      from by decide +kernel)
  obtain ⟨result, tag, equation, _, _⟩ := allowed
  have negativeOne := Value.int.inj tag
  omega

example : ¬ ArtifactTotalCorrect changedArtifact triangularContract :=
  fun correct => changed_artifact_rejected correct.to_partial

#print axioms Examples.Triangular.Arithmetic.preserve
#print axioms Examples.Triangular.Arithmetic.decrease
#print axioms Examples.Triangular.entry
#print axioms Examples.Triangular.body
#print axioms Examples.Triangular.iteration
#print axioms Examples.Triangular.loop_total
#print axioms triangular_total
#print axioms triangular_contract_total
#print axioms triangular_artifact_total
#print axioms triangular_no_exception
#print axioms triangular_no_fault
#print axioms all_natural_inputs
#print axioms zero_result
#print axioms nonnegative_precondition_needed
#print axioms changed_artifact_rejected

end VeriPyAsm.Tests.Triangular
