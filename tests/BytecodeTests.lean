import VeriPyAsm.Examples.Bytecode

deriving instance DecidableEq for Except

namespace VeriPyAsm.Tests

open Semantics CPython.V314 Embedding Examples

/-- Test observation deliberately hides internal frames; return tags are retained. -/
inductive Observation where
  | returned (value : Value)
  | raised (exception : PythonException)
  | fault (reason : Fault)
  | exhausted
  deriving Repr, DecidableEq

def observe (artifact : Artifact) (args : List Value) (fuel : Nat := 1000) :
    Except DecodeError Observation := do
  let translation ← translate artifact
  let frame : Frame :=
    { locals := args.map some ++ List.replicate (artifact.localNames.length - args.length) none }
  pure <| match run (step translation.program) fuel frame with
    | .halted (.returned value _) => .returned value
    | .halted (.raised exception _) => .raised exception
    | .halted (.fault reason _) => .fault reason
    | .exhausted _ => .exhausted

-- Python's bool/int interaction and error cases, including unbound checked locals.
example : observe add1Artifact [.bool true] = .ok (.returned (.int 2)) := by decide
example : observe add1Artifact [.none] = .ok (.raised .typeError) := by decide
example : observe checkedArtifact [.bool false] = .ok (.raised .unboundLocalError) := by decide
example : observe checkedArtifact [.int 7] = .ok (.returned (.int 1)) := by decide
example : observe countdownArtifact [.int (-3)] = .ok (.returned (.int (-3))) := by decide
example : observe chooseArtifact [.none, .int 8, .bool true] =
    .ok (.returned (.bool true)) := by decide
example : observe countdownArtifact [.int 3] 0 = .ok .exhausted := by decide

-- These states expose the difference between a Python exception and a VM fault.
example : Command.load false 2 0 { locals := [none] } =
    .halted (.fault (.unboundUncheckedLocal 0) { locals := [none] }) := by decide
example : Command.branch 2 4 { stack := [.int 1] } =
    .halted (.fault .expectedBool { stack := [.int 1] }) := by decide
example : Command.binary 2 (Semantics.binary .sub) {} =
    .halted (.fault .stackUnderflow {}) := by decide

-- Noncommutative operand order and scalar comparison behavior.
example : Command.binary 2 (Semantics.binary .sub) { stack := [.int 3, .int 10] } =
    .next { pc := 2, stack := [.int 7] } := by decide
example : Semantics.compare .eq (.bool true) (.int 1) = .ok (.bool true) := by decide
example : Semantics.compare .lt .none (.int 1) = .error .typeError := by decide

-- Actual branch fallthrough skips NOT_TAKEN; caches are not executable labels.
example : referenceStep countdown.code
    { pc := 10, stack := [.bool true] } = .next { pc := 16 } := by decide
example : referenceStep countdown.code
    { pc := 10, stack := [.bool false] } = .next { pc := 38 } := by decide
example : referenceStep countdown.code { pc := 34 } = .next { pc := 2 } := by decide
example : fetch countdown.code.instructions 12 = none := by decide

def rejection (artifact : Artifact) : Option DecodeError :=
  match decode artifact with
  | .error error => some error
  | .ok _ => none

example : rejection { add1Artifact with version := ⟨3, 13, 0⟩ } =
    some ⟨0, "expected CPython 3.14.4"⟩ := by decide
example : rejection { add1Artifact with flags := 131 } =
    some ⟨0, "only ordinary optimized function flags (3) are supported"⟩ := by decide
example : rejection { add1Artifact with exceptionTable := [0] } =
    some ⟨0, "exception handlers are not supported"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 86] } =
    some ⟨2, "truncated code unit"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 300, 0] } =
    some ⟨2, "byte outside 0..255"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 69, 1] } =
    some ⟨2, "EXTENDED_ARG is not supported in this slice"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 87, 0] } =
    some ⟨2, "unsupported opcode 87"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 0, 0] } =
    some ⟨2, "CACHE outside an instruction's cache payload"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 44, 0, 0, 0] } =
    some ⟨2, "truncated inline cache"⟩ := by decide
example : rejection { add1Artifact with code := add1Artifact.code.set 8 1 } =
    some ⟨6, "expected zero baseline cache payload"⟩ := by decide
example : rejection { add1Artifact with code := add1Artifact.code.set 3 1 } =
    some ⟨2, "local index out of bounds"⟩ := by decide
example : rejection { literalArtifact with code := [128, 0, 82, 1, 35, 0] } =
    some ⟨2, "constant index out of bounds"⟩ := by decide
example : rejection { countdownArtifact with code := countdownArtifact.code.set 11 0 } =
    none := by decide -- a zero-distance forward target is an instruction boundary
example : rejection { countdownArtifact with code := countdownArtifact.code.set 11 4 } =
    some ⟨10, "control-flow target 22 is not an instruction boundary"⟩ := by decide
example : rejection { countdownArtifact with code := countdownArtifact.code.set 35 30 } =
    some ⟨34, "backward jump before start of code"⟩ := by decide
example : rejection { add1Artifact with code := [128, 0, 94, 1] } =
    some ⟨2, "control-flow target 4 is not an instruction boundary"⟩ := by decide
example : rejection { countdownArtifact with code := countdownArtifact.code.set 7 149 } =
    some ⟨6, "invalid COMPARE_OP comparison mask"⟩ := by decide
example : rejection { add1Artifact with code := add1Artifact.code.set 7 2 } =
    some ⟨6, "unsupported BINARY_OP argument 2"⟩ := by decide

-- A genuine cycle exhausts fuel without being mistaken for an exception/return.
example : observe { literalArtifact with code := [128, 0, 75, 2, 0, 0] } [] 20 =
    .ok .exhausted := by decide +kernel

-- The term elaborator must reject unsupported bytes, and its certificate cannot
-- be reassigned to a changed artifact.
example : True := by
  fail_if_success
    let _ := bytecode% { add1Artifact with code := [128, 0, 69, 1] }
  trivial

example : True := by
  fail_if_success
    have _ : Translation { add1Artifact with code := add1Artifact.code.set 5 2 } := add1
  trivial

-- Exact correspondence is general in the code, fuel and state, not a tested input.
example (code : Code) (fuel : Nat) (s : Frame) :
    run (step (compile code)) fuel s = run (referenceStep code) fuel s :=
  compile_run code fuel s

#print axioms compile_correct
#print axioms compile_run
#print axioms add1_representation

end VeriPyAsm.Tests
