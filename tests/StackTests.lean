import VeriPyAsm.CPython.V314.Stack.Analyze
import VeriPyAsm.Examples.Bytecode

/-! Stack-admission regressions. Handwritten decoded code isolates the stack
analysis from byte decoding; the stored CPython fixtures exercise their boundary.
Tests retain dynamic Python exceptions as valid execution outcomes. -/

namespace VeriPyAsm.Tests.StackAnalysis

open Semantics CPython.V314 CPython.V314.Stack

private def instruction (offset : Nat) (op : Op) (next : Nat := offset + 2) :
    Instruction :=
  { offset, next, opcode := 0, arg := 0, op }

private def accepted (code : Code) (capacity : Nat) : Bool :=
  match analyze code capacity with
  | .ok _ => true
  | .error _ => false

private def rejection (code : Code) (capacity : Nat) : Option Stack.Error :=
  match analyze code capacity with
  | .ok _ => none
  | .error error => some error

/-- Join diagnostics need not depend on the worklist's traversal order. -/
private def joinRejectedAt (code : Code) (capacity offset : Nat) : Bool :=
  match rejection code capacity with
  | some ⟨pc, .inconsistentJoin expected actual⟩ => pc == offset && expected != actual
  | _ => false

-- Real decoded artifacts remain admitted at their actual co_stacksize.
example : accepted Examples.add1.code Examples.add1Artifact.stackSize = true := by decide +kernel
example : accepted Examples.countdown.code Examples.countdownArtifact.stackSize = true := by decide +kernel
example : accepted Examples.choose.code Examples.chooseArtifact.stackSize = true := by decide +kernel
example : accepted Examples.checked.code Examples.checkedArtifact.stackSize = true := by decide +kernel
example : accepted Examples.literal.code Examples.literalArtifact.stackSize = true := by decide +kernel
example : rejection Examples.add1.code 0 = some ⟨2, .capacityExceeded 1 0⟩ := by decide +kernel
example : rejection Examples.add1.code 1 = some ⟨4, .capacityExceeded 2 1⟩ := by decide +kernel

-- Required depth is independent of net stack effect.
example : rejection ⟨[instruction 0 .toBool, instruction 2 .returnValue]⟩ 1 =
    some ⟨0, .underflow 1 0⟩ := by decide
example : rejection ⟨[instruction 0 (.loadSmallInt 1), instruction 2 (.binary .add),
    instruction 4 .returnValue]⟩ 2 = some ⟨2, .underflow 2 1⟩ := by decide
example : rejection ⟨[instruction 0 (.loadSmallInt 1), instruction 2 (.compare .eq),
    instruction 4 .returnValue]⟩ 2 = some ⟨2, .underflow 2 1⟩ := by decide
example : rejection ⟨[instruction 0 (.storeFast 0), instruction 2 (.jump 2)]⟩ 1 =
    some ⟨0, .underflow 1 0⟩ := by decide
example : rejection ⟨[instruction 0 (.popJumpIfFalse 2 4),
    instruction 2 (.jump 2), instruction 4 (.jump 4)]⟩ 1 =
    some ⟨0, .underflow 1 0⟩ := by decide
example : rejection ⟨[instruction 0 (.popJumpIfTrue 2 4),
    instruction 2 (.jump 2), instruction 4 (.jump 4)]⟩ 1 =
    some ⟨0, .underflow 1 0⟩ := by decide

-- RETURN_VALUE requires exactly one value, including rejection of excess values.
example : rejection ⟨[instruction 0 .returnValue]⟩ 1 =
    some ⟨0, .invalidReturnHeight 0⟩ := by decide
example : rejection ⟨[instruction 0 (.loadSmallInt 1), instruction 2 (.loadSmallInt 2),
    instruction 4 .returnValue]⟩ 2 = some ⟨4, .invalidReturnHeight 2⟩ := by decide

private def diamond : Code := ⟨[
  instruction 0 (.loadConst (.bool false)),
  instruction 2 (.popJumpIfFalse 8 4),
  instruction 4 (.loadSmallInt 1),
  instruction 6 (.jump 12),
  instruction 8 (.loadSmallInt 2),
  instruction 10 (.jump 12),
  instruction 12 .returnValue]⟩

example : accepted diamond 1 = true := by decide

-- Both paths are individually legal at the meeting point, but disagree on height.
private def inconsistentDiamond : Code := ⟨[
  instruction 0 (.loadConst (.bool false)),
  instruction 2 (.popJumpIfFalse 8 4),
  instruction 4 (.loadSmallInt 1),
  instruction 6 (.jump 12),
  instruction 8 (.jump 12),
  instruction 12 (.jump 12)]⟩

example : joinRejectedAt inconsistentDiamond 1 12 = true := by decide

private def growingLoop : Code := ⟨[
  instruction 0 .resume,
  instruction 2 (.loadSmallInt 1),
  instruction 4 (.jump 2)]⟩

example : rejection growingLoop 1 = some ⟨2, .inconsistentJoin 0 1⟩ := by decide
example : accepted ⟨[instruction 0 (.jump 0)]⟩ 0 = true := by decide

-- Missing code is diagnosed; stack-invalid dead code need not have a height.
example : rejection ⟨[]⟩ 0 = some ⟨0, .missingInstruction⟩ := by decide
example : rejection ⟨[instruction 0 (.jump 2)]⟩ 0 =
    some ⟨2, .missingInstruction⟩ := by decide
example : accepted ⟨[instruction 0 (.loadSmallInt 1), instruction 2 .returnValue,
    instruction 4 .toBool, instruction 6 .returnValue]⟩ 1 = true := by decide

-- The analysis does not reject programs merely because a Python exception can
-- arise. These two well-shaped programs really do raise in the modeled machine.
private def checkedUnbound : Code := ⟨[
  instruction 0 (.loadFastCheck 0), instruction 2 .returnValue]⟩

example : accepted checkedUnbound 1 = true := by decide
example : referenceStep checkedUnbound { locals := [none] } =
    .halted (.raised .unboundLocalError { locals := [none] }) := by decide

private def raisesTypeError : Code := ⟨[
  instruction 0 (.loadConst .none), instruction 2 (.loadSmallInt 1),
  instruction 4 (.binary .add), instruction 6 .returnValue]⟩

example : accepted raisesTypeError 2 = true := by decide
example : run (referenceStep raisesTypeError) 4 {} =
    .halted (.raised .typeError { pc := 4, stack := [.int 1, .none] }) := by decide

-- Type checking is separate too: accepting the shape must not conceal the
-- explicit expectedBool fault of a non-Boolean branch condition.
private def nonBoolBranch : Code := ⟨[
  instruction 0 (.loadSmallInt 1), instruction 2 (.popJumpIfFalse 4 4),
  instruction 4 (.jump 4)]⟩

example : accepted nonBoolBranch 1 = true := by decide
example : run (referenceStep nonBoolBranch) 3 {} =
    .halted (.fault .expectedBool { pc := 2, stack := [.int 1] }) := by decide

end VeriPyAsm.Tests.StackAnalysis
