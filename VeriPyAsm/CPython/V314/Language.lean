import VeriPyAsm.CPython.V314.Artifact
import VeriPyAsm.Semantics.Fused

/-! Decoded reference language. The raw opcode/argument and byte offsets remain
available even when an operand is resolved to a value or an absolute target. -/

namespace VeriPyAsm.CPython.V314

open Semantics

inductive Op where
  | resume | notTaken
  | loadConst (value : Value)
  | loadSmallInt (value : Nat)
  | loadFast (index : Nat)
  | loadFastBorrow (index : Nat)
  | loadFastCheck (index : Nat)
  | storeFast (index : Nat)
  | loadFastLoadFast (first second : Nat)
  | loadFastBorrowLoadFastBorrow (first second : Nat)
  | storeFastLoadFast (storeIndex loadIndex : Nat)
  | storeFastStoreFast (first second : Nat)
  | binary (operation : BinaryOp)
  | compare (operation : CompareOp)
  | toBool
  | jump (target : Nat)
  | popJumpIfFalse (target fallthrough : Nat)
  | popJumpIfTrue (target fallthrough : Nat)
  | returnValue
  deriving Repr, DecidableEq

structure Instruction where
  offset : Nat
  next : Nat
  opcode : Nat
  arg : Nat
  op : Op
  deriving Repr, DecidableEq

structure Code where
  instructions : List Instruction
  deriving Repr, DecidableEq

/-- All normal control-flow successors, including both conditional edges.
Terminal returns/exceptions have no normal successor. -/
def Instruction.successors (i : Instruction) : List Nat :=
  match i.op with
  | .returnValue => []
  | .jump target => [target]
  | .popJumpIfFalse target fallthrough | .popJumpIfTrue target fallthrough =>
    [target, fallthrough]
  | _ => [i.next]

/-- Instruction semantics shared with the shallow combinators. Borrowing is
unobservable only within the stated scalar/runtime profile. -/
def Instruction.denote (i : Instruction) : Command :=
  match i.op with
  | .resume | .notTaken => Command.jump i.next
  | .loadConst value => Command.push i.next value
  | .loadSmallInt value => Command.push i.next (.int (Int.ofNat value))
  | .loadFast index | .loadFastBorrow index => Command.load false i.next index
  | .loadFastCheck index => Command.load true i.next index
  | .storeFast index => Command.store i.next index
  | .loadFastLoadFast first second | .loadFastBorrowLoadFastBorrow first second =>
    Command.loadPair i.next first second
  | .storeFastLoadFast storeIndex loadIndex => Command.storeLoad i.next storeIndex loadIndex
  | .storeFastStoreFast first second => Command.storePair i.next first second
  | .binary op => Command.binary i.next (Semantics.binary op)
  | .compare op => Command.binary i.next (Semantics.compare op)
  | .toBool => Command.toBool i.next
  | .jump target => Command.jump target
  | .popJumpIfFalse target fallthrough => Command.branch fallthrough target
  | .popJumpIfTrue target fallthrough => Command.branch target fallthrough
  | .returnValue => Command.ret

def fetch : List Instruction → Nat → Option Instruction
  | [], _ => none
  | i :: rest, pc => if pc = i.offset then some i else fetch rest pc

/-- Reference dispatch over decoded instructions, before shallow translation. -/
def referenceStep (code : Code) (s : Frame) : StepResult :=
  match fetch code.instructions s.pc with
  | some i => i.denote s
  | none => .halted (.fault (.invalidPC s.pc) s)

end VeriPyAsm.CPython.V314
