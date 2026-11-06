import VeriPyAsm.Examples.Assertions.Artifact
import VeriPyAsm.Verification.Instruction
import VeriPyAsm.Verification.VC.WeakestPrecondition

/-! Bare assertion semantics and conservative admission. Crafted rejected
artifacts are checked in Lean only; they are never executed by CPython. -/

namespace VeriPyAsm.Tests.Assertions

open Semantics CPython.V314 Verification Examples.Assertions

-- Failure frames retain the instruction-entry snapshot, including the marker.
example : run (step nonnegative.translation.program) 7 { locals := [some (.int 3)] } =
    .halted (.returned (.int 3) { pc := 22, locals := [some (.int 3)] }) := by decide +kernel

example : run (step nonnegative.translation.program) 7 { locals := [some (.int (-1))] } =
    .halted (.raised .assertionError
      { pc := 18, locals := [some (.int (-1))], stack := [.assertionErrorType] }) := by decide +kernel

example : run (step nonnegative.translation.program) 7 { locals := [some .none] } =
    .halted (.raised .typeError
      { pc := 6, locals := [some .none], stack := [.int 0, .none] }) := by decide +kernel

example : run (step alwaysFails.translation.program) 3 {} =
    .halted (.raised .assertionError { pc := 4, stack := [.assertionErrorType] }) := by decide +kernel

example : Command.raiseAssertionError { stack := [.int 0] } =
    .halted (.fault .expectedAssertionErrorType { stack := [.int 0] }) := rfl

example : Command.raiseAssertionError {} = .halted (.fault .stackUnderflow {}) := rfl

example (rest : List Value) :
    InstructionCorrect Command.raiseAssertionError
      (fun s => s.stack = .assertionErrorType :: rest)
      { raises := fun e s => e = .assertionError ∧ s.stack = .assertionErrorType :: rest } := by
  apply (InstructionCorrect.raiseAssertionError
    { raises := fun e s => e = .assertionError ∧ s.stack = .assertionErrorType :: rest }).consequence
  · intro s stack
    exact ⟨rest, stack, rfl, stack⟩
  · exact fun _ h => h

-- Failure cannot be turned into an assumption, even with a permissive return.
example : VC.wp Command.raiseAssertionError [] { returned := fun _ _ => True } 1
    { stack := [.assertionErrorType] } = False := rfl

example : Ownership.transfer .loadAssertionError [.borrowed 0] =
    .ok [.owned, .borrowed 0] := rfl
example : Ownership.transfer .raiseAssertionError [.owned, .borrowed 0] =
    .ok [.borrowed 0] := rfl
example : Ownership.transfer .raiseAssertionError [.borrowed 0] =
    .error (.raiseBorrow 0) := rfl

private def raiseInstruction : Instruction := ⟨4, 6, 104, 1, .raiseAssertionError⟩
example : raiseInstruction.successors = [] := rfl
example : ¬ raiseInstruction.StackReady 0 := by decide
example : raiseInstruction.StackReady 2 := by decide

private def rejection (artifact : Artifact) : Option AdmissionError :=
  match admit artifact with
  | .ok _ => none
  | .error error => some error

example : rejection { nonnegativeArtifact with stackSize := 1 } =
    some (.stack ⟨4, .capacityExceeded 2 1⟩) := by decide +kernel
example : rejection { alwaysFailsArtifact with stackSize := 0 } =
    some (.stack ⟨2, .capacityExceeded 1 0⟩) := by decide +kernel

private def decodeRejection (artifact : Artifact) : Option DecodeError :=
  match decode artifact with
  | .ok _ => none
  | .error error => some error

example : decodeRejection { nonnegativeArtifact with code := nonnegativeArtifact.code.set 17 1 } =
    some ⟨16, "only LOAD_COMMON_CONSTANT 0 (AssertionError) is supported"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with code := nonnegativeArtifact.code.set 19 0 } =
    some ⟨18, "only RAISE_VARARGS 1 for bare assertions is supported"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with code := nonnegativeArtifact.code.set 19 2 } =
    some ⟨18, "only RAISE_VARARGS 1 for bare assertions is supported"⟩ := by decide +kernel

-- The marker is not a code-object constant or a general object/call interface.
example : decodeRejection { nonnegativeArtifact with constants := [.assertionErrorType] } =
    some ⟨0, "code-object constants must be scalar literals"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with code := [128, 0, 81, 0, 35, 0] } =
    some ⟨2, "AssertionError load must be followed immediately by RAISE_VARARGS 1"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with
    code := [128, 0, 81, 0, 112, 0, 94, 1, 35, 0] } =
    some ⟨2, "AssertionError load must be followed immediately by RAISE_VARARGS 1"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with code := [128, 0, 94, 0, 104, 1] } =
    some ⟨4, "RAISE_VARARGS 1 requires an immediately preceding AssertionError load"⟩ := by decide +kernel

-- A join at RAISE could have the right height but the wrong value. Require all
-- incoming edges, even unreachable ones, to pass through the class load.
example : decodeRejection { nonnegativeArtifact with
    code := [128, 0, 94, 0, 77, 1, 81, 0, 104, 1] } =
    some ⟨4, "control flow may not bypass the AssertionError load"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with
    code := [128, 0, 94, 1, 35, 0, 81, 0, 35, 0] } =
    some ⟨6, "AssertionError load must be followed immediately by RAISE_VARARGS 1"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with
    code := [128, 0, 94, 1, 35, 0, 104, 1] } =
    some ⟨6, "RAISE_VARARGS 1 requires an immediately preceding AssertionError load"⟩ := by decide +kernel

-- Optimized assertions, NOP-folded assertions, and constructor calls stay out.
example : decodeRejection { nonnegativeArtifact with optimize := 1 } =
    some ⟨0, "expected optimize=0"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with code := [128, 0, 27, 0, 84, 0, 35, 0] } =
    some ⟨2, "unsupported opcode 27"⟩ := by decide +kernel
example : decodeRejection { nonnegativeArtifact with
    code := [128, 0, 81, 0, 94, 1, 52, 0, 0, 0, 0, 0, 0, 0, 104, 1] } =
    some ⟨6, "unsupported opcode 52"⟩ := by decide +kernel
example : decodeRejection { alwaysFailsArtifact with code := alwaysFailsArtifact.code ++ [52, 0] } =
    some ⟨6, "unsupported opcode 52"⟩ := by decide +kernel

#veripy_audit VeriPyAsm.Tests.Assertions

end VeriPyAsm.Tests.Assertions
