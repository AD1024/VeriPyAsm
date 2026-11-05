import VeriPyAsm.Examples.Bytecode

/-! Artifact-level tests: the code, raw-byte decoding certificate, and declared
capacity remain connected through both runtime and elaboration-time admission. -/

namespace VeriPyAsm.Tests.Admission

open Semantics CPython.V314 Embedding Examples

def admittedAdd1 : StackAdmitted add1Artifact := admit_bytecode% add1Artifact
def admittedCountdown : StackAdmitted countdownArtifact := admit_bytecode% countdownArtifact
def admittedChoose : StackAdmitted chooseArtifact := admit_bytecode% chooseArtifact
def admittedChecked : StackAdmitted checkedArtifact := admit_bytecode% checkedArtifact
def admittedLiteral : StackAdmitted literalArtifact := admit_bytecode% literalArtifact

theorem add1_certificate_valid :
    Stack.Valid admittedAdd1.translation.code add1Artifact.stackSize admittedAdd1.stack.heights :=
  admittedAdd1.stack.valid

example : admittedCountdown.translation.code = countdown.code := rfl
example : admittedChoose.translation.code = choose.code := rfl
example : admittedChecked.translation.code = checked.code := rfl
example : admittedLiteral.translation.code = literal.code := rfl

private def accepted (artifact : Artifact) : Bool :=
  match admit artifact with
  | .ok _ => true
  | .error _ => false

private def rejection (artifact : Artifact) : Option AdmissionError :=
  match admit artifact with
  | .ok _ => none
  | .error error => some error

example : accepted add1Artifact = true := by decide +kernel
example : accepted countdownArtifact = true := by decide +kernel
example : accepted chooseArtifact = true := by decide +kernel
example : accepted checkedArtifact = true := by decide +kernel
example : accepted literalArtifact = true := by decide +kernel
example : rejection { add1Artifact with stackSize := 1 } =
    some (.stack ⟨4, .capacityExceeded 2 1⟩) := by decide +kernel
example : rejection { add1Artifact with code := [128, 0, 69, 1] } =
    some (.decode ⟨2, "dangling EXTENDED_ARG"⟩) := by decide

private def emptyReturn : Artifact :=
  { add1Artifact with code := [128, 0, 35, 0] }

private def excessReturn : Artifact :=
  { add1Artifact with code := [128, 0, 94, 1, 94, 2, 35, 0] }

example : rejection emptyReturn = some (.stack ⟨2, .invalidReturnHeight 0⟩) := by decide
example : rejection excessReturn = some (.stack ⟨6, .invalidReturnHeight 2⟩) := by decide

-- Translation alone retains its original meaning; it does not assert stack safety.
private def translationOnly : Translation emptyReturn := bytecode% emptyReturn
example : decode emptyReturn = .ok translationOnly.code := translationOnly.decoded

/-- error: stack admission rejected: byte offset 4: stack height 2 exceeds co_stacksize 1 -/
#guard_msgs in
#check admit_bytecode% { add1Artifact with stackSize := 1 }

example : True := by
  fail_if_success
    let _ := admit_bytecode% emptyReturn
  trivial

example : True := by
  fail_if_success
    let _ := admit_bytecode% excessReturn
  trivial

-- Certificates cannot silently follow changed capacities or changed raw bytes,
-- even when a fresh analysis of the modified artifact might succeed.
example : True := by
  fail_if_success
    have _ : StackAdmitted { add1Artifact with stackSize := 3 } := admittedAdd1
  trivial

example : True := by
  fail_if_success
    have _ : StackAdmitted { add1Artifact with code := add1Artifact.code.set 5 2 } := admittedAdd1
  trivial

example : True := by
  fail_if_success
    have _ : Stack.Certificate admittedAdd1.translation.code 1 := admittedAdd1.stack
  trivial

-- These wrappers quantify over every fuel bound and entry-local assignment.
-- They are structural facts, not just executions at selected test inputs.
theorem add1_no_underflow (fuel : Nat) (locals : List (Option Value)) (failureFrame : Frame) :
    run (step admittedAdd1.translation.program) fuel { locals } ≠
      .halted (.fault .stackUnderflow failureFrame) :=
  admittedAdd1.run_no_underflow fuel locals failureFrame

theorem countdown_continuation_bound (fuel : Nat) (locals : List (Option Value))
    (continuation : Frame)
    (execution : run (step admittedCountdown.translation.program) fuel { locals } =
      .exhausted continuation) : continuation.stack.length ≤ 2 :=
  admittedCountdown.run_exhausted_bound fuel locals continuation execution

theorem add1_return_empty (fuel : Nat) (locals : List (Option Value))
    (value : Value) (finalFrame : Frame)
    (execution : run (step admittedAdd1.translation.program) fuel { locals } =
      .halted (.returned value finalFrame)) : finalFrame.stack = [] :=
  admittedAdd1.run_return_stack fuel locals value finalFrame execution

#print axioms StackAdmitted.run_no_underflow
#print axioms StackAdmitted.run_exhausted_bound
#print axioms StackAdmitted.run_return_stack
#print axioms admittedAdd1
#print axioms add1_certificate_valid
#print axioms add1_no_underflow
#print axioms countdown_continuation_bound
#print axioms add1_return_empty

end VeriPyAsm.Tests.Admission
