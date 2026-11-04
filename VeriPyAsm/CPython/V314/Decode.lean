import VeriPyAsm.CPython.V314.Language

/-! Conservative decoder for CPython 3.14.4 baseline code. Cache words are payload;
they never become instructions. EXTENDED_ARG, fused/specialized instructions, and
code-object features outside this first slice are rejected explicitly.

This checks encoding, metadata, operand bounds, and control-flow boundaries.
It does NOT yet prove stack-height consistency or definite initialization. -/

namespace VeriPyAsm.CPython.V314

open Semantics

structure DecodeError where
  offset : Nat
  reason : String
  deriving Repr, DecidableEq

private def fail {α : Type} (offset : Nat) (reason : String) : Except DecodeError α :=
  .error { offset, reason }

private def check (condition : Bool) (offset : Nat) (reason : String) :
    Except DecodeError Unit :=
  if condition then .ok () else fail offset reason

private def checkMetadata (a : Artifact) : Except DecodeError Unit := do
  check (a.schemaVersion == 1) 0 "unsupported artifact schema"
  check (a.implementation == "cpython" && a.version == targetPythonVersion)
    0 "expected CPython 3.14.4"
  check (a.profile == .baselineSequential) 0 "unsupported runtime profile"
  check (!a.build.isEmpty) 0 "missing interpreter build identity"
  check (a.optimize == 0) 0 "expected optimize=0"
  check (a.flags == 3) 0 "only ordinary optimized function flags (3) are supported"
  check (a.kwOnlyArgCount == 0 && a.posOnlyArgCount ≤ a.argCount &&
    a.argCount ≤ a.localNames.length) 0 "unsupported or inconsistent argument metadata"
  check (a.names.isEmpty && a.freeVars.isEmpty && a.cellVars.isEmpty)
    0 "names, globals, and closures are not supported"
  check a.exceptionTable.isEmpty 0 "exception handlers are not supported"
  check (!a.code.isEmpty) 0 "empty bytecode"
  check (a.code.length % 2 == 0) (a.code.length - 1) "truncated code unit"
  for (byte, offset) in a.code.zipIdx do
    check (byte < 256) offset "byte outside 0..255"

/-- Widths from the pinned instruction definitions, in two-byte cache words. -/
private def cacheWords : Nat → Nat
  | 44 => 5 -- BINARY_OP
  | 39 => 3 -- TO_BOOL
  | 56 | 75 | 100 | 103 => 1
  | _ => 0

private def decodeBinary (pc arg : Nat) : Except DecodeError BinaryOp :=
  match arg with
  | 0 | 13 => .ok .add
  | 10 | 23 => .ok .sub
  | 5 | 18 => .ok .mul
  | _ => fail pc s!"unsupported BINARY_OP argument {arg}"

private def decodeCompare (pc arg : Nat) : Except DecodeError CompareOp := do
  let (op, mask) ← match arg / 32 with
    | 0 => pure (CompareOp.lt, 2)
    | 1 => pure (CompareOp.le, 10)
    | 2 => pure (CompareOp.eq, 8)
    | 3 => pure (CompareOp.ne, 7)
    | 4 => pure (CompareOp.gt, 4)
    | 5 => pure (CompareOp.ge, 12)
    | _ => fail pc s!"invalid COMPARE_OP argument {arg}"
  check (arg % 16 == mask) pc "invalid COMPARE_OP comparison mask"
  -- Bit 4 requests bool coercion. Scalar rich comparisons already return bool.
  pure op

private def decodeOp (a : Artifact) (pc next opcode arg : Nat) :
    Except DecodeError Op := do
  let checkLocal := check (arg < a.localNames.length) pc "local index out of bounds"
  let noArg := check (arg == 0) pc "expected zero unused argument"
  -- CPython skips a following NOT_TAKEN on the untaken branch.
  let fallthrough := if a.code[next]? == some 28 then next + 2 else next
  match opcode with
  | 128 =>
    check (pc == 0 && arg == 0) pc "only entry RESUME 0 is supported"
    pure .resume
  | 28 => noArg; pure .notTaken
  | 82 => match a.constants[arg]? with
    | some value => pure (.loadConst value)
    | none => fail pc "constant index out of bounds"
  | 94 => pure (.loadSmallInt arg)
  | 84 => checkLocal; pure (.loadFast arg)
  | 86 => checkLocal; pure (.loadFastBorrow arg)
  | 88 => checkLocal; pure (.loadFastCheck arg)
  | 112 => checkLocal; pure (.storeFast arg)
  | 44 => return .binary (← decodeBinary pc arg)
  | 56 => return .compare (← decodeCompare pc arg)
  | 39 => noArg; pure .toBool
  | 77 => pure (.jump (next + 2 * arg))
  | 75 =>
    check (2 * arg ≤ next) pc "backward jump before start of code"
    pure (.jump (next - 2 * arg))
  | 100 => pure (.popJumpIfFalse (next + 2 * arg) fallthrough)
  | 103 => pure (.popJumpIfTrue (next + 2 * arg) fallthrough)
  | 35 => noArg; pure .returnValue
  | 0 => fail pc "CACHE outside an instruction's cache payload"
  | 69 => fail pc "EXTENDED_ARG is not supported in this slice"
  | _ => fail pc s!"unsupported opcode {opcode}"

private def decodeInstructions (a : Artifact) :
    Nat → Nat → List Nat → Except DecodeError (List Instruction)
  | _, _, [] => pure []
  | 0, pc, _ => fail pc "decoder fuel exhausted"
  | _ + 1, pc, [_] => fail pc "truncated code unit"
  | fuel + 1, pc, opcode :: arg :: rest => do
    let width := 2 * cacheWords opcode
    let next := pc + 2 + width
    let op ← decodeOp a pc next opcode arg
    check (width ≤ rest.length) pc "truncated inline cache"
    check ((rest.take width).all (· == 0)) pc "expected zero baseline cache payload"
    let tail ← decodeInstructions a fuel next (rest.drop width)
    pure ({ offset := pc, next, opcode, arg, op } :: tail)

private def successors (i : Instruction) : List Nat :=
  match i.op with
  | .returnValue => []
  | .jump target => [target]
  | .popJumpIfFalse target fallthrough | .popJumpIfTrue target fallthrough =>
    [target, fallthrough]
  | _ => [i.next]

/-- Decode every instruction (also unreachable ones), checking all target and
fallthrough boundaries. A successful decode is not yet a program-safety proof. -/
def decode (artifact : Artifact) : Except DecodeError Code := do
  checkMetadata artifact
  let instructions ← decodeInstructions artifact artifact.code.length 0 artifact.code
  check (artifact.code[0]? == some 128) 0 "expected entry RESUME"
  for instruction in instructions do
    for target in successors instruction do
      check ((fetch instructions target).isSome) instruction.offset
        s!"control-flow target {target} is not an instruction boundary"
  pure { instructions }

end VeriPyAsm.CPython.V314
