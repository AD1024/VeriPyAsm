import VeriPyAsm.Semantics.Iteration
import VeriPyAsm.Verification.Instruction

/-! Contracts for one nonempty iteration, assembled from an initial instruction
and an ordinary block. The initial cutpoint is deliberately crossed once; all
later cutpoints retain first-exit behavior. -/

namespace VeriPyAsm.Verification

open Semantics

def IterationPartialCorrect (next : Frame → StepResult) (cuts : Nat → Prop)
    (pre : Frame → Prop) (post : Postcondition) : Prop :=
  ∀ initial, pre initial → ∀ result,
    IterationExecutes next cuts initial result → post.Accepts result

structure IterationTotalCorrect (next : Frame → StepResult) (cuts : Nat → Prop)
    (pre : Frame → Prop) (post : Postcondition) : Prop where
  partialCorrect : IterationPartialCorrect next cuts pre post
  terminates : ∀ initial, pre initial → ∃ result, IterationExecutes next cuts initial result

variable {next : Frame → StepResult} {cuts : Nat → Prop}
    {P P' R : Frame → Prop} {Q Q' : Postcondition}

theorem IterationTotalCorrect.of_execution
    (execute : ∀ initial, P initial →
      ∃ result, IterationExecutes next cuts initial result ∧ Q.Accepts result) :
    IterationTotalCorrect next cuts P Q := by
  constructor
  · intro initial pre result execution
    obtain ⟨expected, observed, allowed⟩ := execute initial pre
    have equal := observed.deterministic execution
    cases equal
    exact allowed
  · intro initial pre
    obtain ⟨result, execution, _⟩ := execute initial pre
    exact ⟨result, execution⟩

theorem IterationPartialCorrect.consequence (correct : IterationPartialCorrect next cuts P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ result, Q.Accepts result → Q'.Accepts result) :
    IterationPartialCorrect next cuts P' Q' :=
  fun s h result execution => post result (correct s (pre s h) result execution)

theorem IterationTotalCorrect.consequence (correct : IterationTotalCorrect next cuts P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ result, Q.Accepts result → Q'.Accepts result) :
    IterationTotalCorrect next cuts P' Q' :=
  ⟨correct.partialCorrect.consequence pre post, fun s h => correct.terminates s (pre s h)⟩

theorem InstructionCorrect.start_iteration_partial {command : Command} {program : Program}
    (correct : InstructionCorrect command P { Q with continues := R })
    (fetch : ∀ s, P s → program s.pc = some command)
    (tail : BlockPartialCorrect (step program) cuts R Q) :
    IterationPartialCorrect (step program) cuts P Q := by
  intro s pre result execution
  have allowed := correct s pre
  have dispatch : step program s = command s := by simp only [step, fetch s pre]
  cases execution with
  | @halt outcome transition =>
    rw [← dispatch, transition] at allowed
    cases outcome <;> exact allowed
  | step transition after =>
    rw [← dispatch, transition] at allowed
    exact tail _ allowed _ after

theorem InstructionCorrect.start_iteration {command : Command} {program : Program}
    (correct : InstructionCorrect command P { Q with continues := R })
    (fetch : ∀ s, P s → program s.pc = some command)
    (tail : BlockTotalCorrect (step program) cuts R Q) :
    IterationTotalCorrect (step program) cuts P Q := by
  apply IterationTotalCorrect.of_execution
  intro s pre
  have allowed := correct s pre
  have dispatch : step program s = command s := by simp only [step, fetch s pre]
  cases transition : command s with
  | next frame =>
    rw [transition] at allowed
    obtain ⟨result, execution⟩ := tail.terminates frame allowed
    exact ⟨result, .step (dispatch.trans transition) execution,
      tail.partialCorrect frame allowed result execution⟩
  | halted outcome =>
    rw [transition] at allowed
    refine ⟨.halted outcome, .halt (dispatch.trans transition), ?_⟩
    cases outcome <;> exact allowed

end VeriPyAsm.Verification
