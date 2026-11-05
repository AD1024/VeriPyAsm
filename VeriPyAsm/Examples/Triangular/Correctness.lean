import VeriPyAsm.Examples.Triangular.Blocks
import VeriPyAsm.Examples.Triangular.Arithmetic
import VeriPyAsm.Verification.Artifact
import VeriPyAsm.Verification.Hoare

/-! Universal total correctness of the imported triangular artifact. The proof
composes bytecode summaries with a loop invariant and a natural-number ranking;
no input-specific fuel bound is used. Artifact transport retains the raw bytes
as the theorem's anchor. CPython runtime refinement remains a separate claim. -/

namespace VeriPyAsm.Examples

open Semantics Verification
open scoped VeriPyAsm.Verification.Hoare

namespace Triangular

def invariant (N : Int) (current : Frame) : Prop :=
  ∃ n sum : Int, current = frame 6 n sum ∧ 0 ≤ n ∧
    2 * sum + n * (n + 1) = N * (N + 1)

/-- Only invariant states use this rank. Their first local is a nonnegative int;
the default for other states carries no semantic claim. -/
def rank (current : Frame) : Nat :=
  match current.locals[(0 : Nat)]? with
  | some (some (.int n)) => n.toNat
  | _ => 0

def exitInvariant (N : Int) (current : Frame) : Prop :=
  ∃ sum : Int, current = frame 58 0 sum ∧ 2 * sum = N * (N + 1)

def postcondition (N : Int) : Postcondition :=
  { returned := fun value final => ∃ result : Int,
      value = .int result ∧ 2 * result = N * (N + 1) ∧
      final.locals = [some (.int 0), some (.int result)] ∧ final.stack = [] }

theorem loop_total (N : Int) :
    BlockTotalCorrect (step triangular.translation.program) (fun pc => pc = 58)
      (invariant N) { continues := exitInvariant N } := by
  apply BlockTotalCorrect.loop (cuts := cuts) rank (fun _ h => Or.inr h)
  · rintro current ⟨n, sum, rfl, _, _⟩
    simp [frame]
  · intro initial hypothesis
    obtain ⟨n, sum, equal, nonnegative, equation⟩ := hypothesis
    subst initial
    apply (iteration n sum).consequence (fun _ h => h)
    intro result allowed
    cases result with
    | next current =>
      rcases allowed with ⟨positive, equal⟩ | ⟨nonpositive, equal⟩
      · subst current
        exact Or.inr ⟨⟨n - 1, sum + n, rfl, (Arithmetic.decrease n positive).1,
          Arithmetic.preserve N n sum equation⟩, (Arithmetic.decrease n positive).2⟩
      · have resultEquation := Arithmetic.at_exit N n sum nonnegative nonpositive equation
        have zero : n = 0 := by omega
        subst n
        subst current
        exact Or.inl ⟨rfl, sum, rfl, resultEquation⟩
    | halted outcome => cases outcome <;> exact False.elim allowed

theorem finish_total (N : Int) :
    BlockTotalCorrect (step triangular.translation.program) (fun _ => False)
      (exitInvariant N) (postcondition N) := by
  apply BlockTotalCorrect.of_execution
  rintro initial ⟨sum, equal, equation⟩
  subst initial
  have correct := finish 0 sum
  obtain ⟨result, execution⟩ := correct.terminates (frame 58 0 sum) rfl
  have allowed := correct.partialCorrect _ rfl result execution
  refine ⟨result, execution, ?_⟩
  cases result with
  | next current => exact False.elim allowed
  | halted outcome =>
    cases outcome with
    | returned value final =>
      rcases allowed with ⟨rfl, rfl⟩
      exact ⟨sum, rfl, equation, rfl, rfl⟩
    | raised _ _ => exact False.elim allowed
    | fault _ _ => exact False.elim allowed

theorem program_total (N : Int) (nonnegative : 0 ≤ N) :
    BlockTotalCorrect (step triangular.translation.program) (fun _ => False)
      (fun initial => initial = { locals := [some (.int N), none] }) (postcondition N) := by
  have loop : BlockTotalCorrect (step triangular.translation.program) (fun pc => pc = 58)
      (invariant N) { postcondition N with continues := exitInvariant N } := by
    apply (loop_total N).consequence (fun _ h => h)
    intro result allowed
    cases result with
    | next current => exact allowed
    | halted outcome => cases outcome <;> exact False.elim allowed
  have suffix := loop.seq (finish_total N) (fun _ impossible => False.elim impossible)
  have first : BlockTotalCorrect (step triangular.translation.program) (fun pc => pc = 6)
      (fun initial => initial = { locals := [some (.int N), none] })
      { postcondition N with continues := invariant N } := by
    apply (entry N).consequence (fun _ h => h)
    intro result allowed
    cases result with
    | next current =>
      change current = frame 6 N 0 at allowed
      subst current
      exact ⟨N, 0, rfl, nonnegative, Arithmetic.at_entry N⟩
    | halted outcome => cases outcome <;> exact False.elim allowed
  exact first.seq suffix (fun _ impossible => False.elim impossible)

end Triangular

/-- Nonnegative exact integers are accepted. The return equation avoids any
division convention, and the final locals record the exhausted counter and sum. -/
def triangularContract : Contract Int where
  pre N initial := 0 ≤ N ∧ initial = { locals := [some (.int N), none] }
  post N _ := (Triangular.postcondition N).returned
  raises _ _ _ _ := False

theorem triangular_total (N : Int) :
    {{ fun initial => 0 ≤ N ∧ initial = { locals := [some (.int N), none] } }}
      triangular.translation.program
    {{ returns fun value final => ∃ result : Int,
      value = .int result ∧ 2 * result = N * (N + 1) ∧
      final.locals = [some (.int 0), some (.int result)] ∧ final.stack = [] }} := by
  apply TotalCorrect.of_execution
  intro _ initial pre
  change 0 ≤ N ∧ initial = { locals := [some (.int N), none] } at pre
  obtain ⟨nonnegative, equal⟩ := pre
  subst initial
  have correct := (Triangular.program_total N nonnegative).to_totalCorrect
  obtain ⟨outcome, execution⟩ :=
    correct.terminates () { locals := [some (.int N), none] } rfl
  exact ⟨outcome, execution, correct.partialCorrect () _ rfl outcome execution⟩

theorem triangular_contract_total :
    TotalCorrect (step triangular.translation.program) triangularContract := by
  apply TotalCorrect.of_execution
  intro N initial pre
  obtain ⟨outcome, execution⟩ := (triangular_total N).terminates () initial pre
  exact ⟨outcome, execution, (triangular_total N).partialCorrect () initial pre outcome execution⟩

theorem triangular_artifact_total : ArtifactTotalCorrect triangularArtifact triangularContract :=
  triangular.translation.artifact_total_iff.mpr triangular_contract_total

theorem triangular_no_exception (N : Int) (nonnegative : 0 ≤ N) (fuel : Nat)
    (exception : PythonException) (failureFrame : Frame) :
    run (step triangular.translation.program) fuel { locals := [some (.int N), none] } ≠
      .halted (.raised exception failureFrame) := by
  intro execution
  exact (triangular_total N).partialCorrect.run_halted (ghost := ()) ⟨nonnegative, rfl⟩ execution

theorem triangular_no_fault (N : Int) (nonnegative : 0 ≤ N) (fuel : Nat)
    (reason : Fault) (failureFrame : Frame) :
    run (step triangular.translation.program) fuel { locals := [some (.int N), none] } ≠
      .halted (.fault reason failureFrame) := by
  intro execution
  exact (triangular_total N).partialCorrect.run_halted (ghost := ()) ⟨nonnegative, rfl⟩ execution

end VeriPyAsm.Examples
