import VeriPyAsm.Embedding
import VeriPyAsm.CPython.V314.Stack.Analyze
import VeriPyAsm.CPython.V314.Stack.Soundness
import VeriPyAsm.CPython.V314.Ownership.Analyze
import VeriPyAsm.CPython.V314.Ownership.Soundness

/-! Artifact-facing admission with separate stack and ownership certificates.
Both are indexed by the exact decoded code; stack capacity also comes from the
artifact. Value tags, initial locals, and contracts remain separate obligations.
Neither certificate is a refinement proof of the CPython C runtime. -/

namespace VeriPyAsm

open Semantics CPython.V314 Embedding

inductive AdmissionError where
  | decode (error : DecodeError)
  | stack (error : Stack.Error)
  | ownership (error : Ownership.Error)
  deriving Repr, DecidableEq

def AdmissionError.message : AdmissionError → String
  | .decode error => s!"byte offset {error.offset}: {error.reason}"
  | .stack error => error.message
  | .ownership error => error.message

structure StackAdmitted (artifact : Artifact) where
  translation : Translation artifact
  stack : Stack.Certificate translation.code artifact.stackSize

structure Admitted (artifact : Artifact) extends StackAdmitted artifact where
  ownership : Ownership.Certificate translation.code

instance {artifact : Artifact} : Coe (Admitted artifact) (StackAdmitted artifact) :=
  ⟨Admitted.toStackAdmitted⟩

/-- Decode, translate, infer stack heights, then check the resulting certificate. -/
def admitStack (artifact : Artifact) : Except AdmissionError (StackAdmitted artifact) := do
  let translation ← (translate artifact).mapError AdmissionError.decode
  let stack ← (Stack.analyze translation.code artifact.stackSize).mapError AdmissionError.stack
  pure ⟨translation, stack⟩

/-- Public admission requires both certificates. Stack-only clients must opt
into `admitStack`; its result cannot supply a missing ownership certificate. -/
def admit (artifact : Artifact) : Except AdmissionError (Admitted artifact) := do
  let structural ← admitStack artifact
  let ownership ← (Ownership.analyze structural.translation.code).mapError AdmissionError.ownership
  pure ⟨structural, ownership⟩

/-- Every reachable instruction has a checked provenance history from entry and
a successful ownership transfer, including the instruction about to halt. -/
theorem Admitted.reachable_ownership {artifact : Artifact} (admitted : Admitted artifact)
    (locals : List (Option Value)) {current : Frame}
    (path : Reaches (step admitted.translation.program) { locals } current) :
    ∃ refs instruction output,
      Ownership.Path admitted.translation.code 0 [] current.pc refs ∧
      fetch admitted.translation.code.instructions current.pc = some instruction ∧
      Ownership.transfer instruction.op refs = .ok output := by
  rw [admitted.translation.correct] at path
  obtain ⟨refs, tracked, known⟩ := admitted.ownership.tracks_reaches admitted.stack path
    (admitted.stack.entry_matches locals) admitted.ownership.valid.1
  obtain ⟨instruction, output, fetched, effect, _⟩ := admitted.ownership.ready known
  exact ⟨refs, instruction, output, tracked, fetched, effect⟩

/-- Every finite execution from the entry frame excludes stack underflow. Other
VM faults and Python exceptions are deliberately not excluded by this theorem. -/
theorem StackAdmitted.run_no_underflow {artifact : Artifact}
    (admitted : StackAdmitted artifact) (fuel : Nat) (locals : List (Option Value))
    (failureFrame : Frame) :
    run (step admitted.translation.program) fuel { locals } ≠
      .halted (.fault .stackUnderflow failureFrame) := by
  rw [admitted.translation.correct]
  exact admitted.stack.run_no_underflow fuel { locals }
    (admitted.stack.entry_matches locals) failureFrame

/-- Any continuation reached from entry respects the artifact's declared capacity. -/
theorem StackAdmitted.run_exhausted_bound {artifact : Artifact}
    (admitted : StackAdmitted artifact) (fuel : Nat) (locals : List (Option Value))
    (continuation : Frame)
    (execution : run (step admitted.translation.program) fuel { locals } =
      .exhausted continuation) : continuation.stack.length ≤ artifact.stackSize := by
  rw [admitted.translation.correct] at execution
  exact admitted.stack.run_exhausted_bound fuel { locals } continuation
    (admitted.stack.entry_matches locals) execution

theorem StackAdmitted.run_return_stack {artifact : Artifact}
    (admitted : StackAdmitted artifact) (fuel : Nat) (locals : List (Option Value))
    (value : Value) (finalFrame : Frame)
    (execution : run (step admitted.translation.program) fuel { locals } =
      .halted (.returned value finalFrame)) : finalFrame.stack = [] := by
  rw [admitted.translation.correct] at execution
  exact admitted.stack.run_return_stack fuel { locals } finalFrame value
    (admitted.stack.entry_matches locals) execution

end VeriPyAsm
