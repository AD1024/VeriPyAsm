import VeriPyAsm.Embedding
import VeriPyAsm.CPython.V314.Stack.Analyze
import VeriPyAsm.CPython.V314.Stack.Soundness

/-! Artifact-facing stack admission. The certificate is indexed by the exact
decoded code and the artifact's co_stacksize. This is stack admission only;
value types, local initialization, and program contracts are separate concerns. -/

namespace VeriPyAsm

open Semantics CPython.V314 Embedding

inductive AdmissionError where
  | decode (error : DecodeError)
  | stack (error : Stack.Error)
  deriving Repr, DecidableEq

def AdmissionError.message : AdmissionError → String
  | .decode error => s!"byte offset {error.offset}: {error.reason}"
  | .stack error => error.message

structure StackAdmitted (artifact : Artifact) where
  translation : Translation artifact
  stack : Stack.Certificate translation.code artifact.stackSize

/-- Decode, translate, infer stack heights, then check the resulting certificate. -/
def admit (artifact : Artifact) : Except AdmissionError (StackAdmitted artifact) := do
  let translation ← (translate artifact).mapError AdmissionError.decode
  let stack ← (Stack.analyze translation.code artifact.stackSize).mapError AdmissionError.stack
  pure ⟨translation, stack⟩

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
