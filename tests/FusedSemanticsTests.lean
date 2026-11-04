import VeriPyAsm.CPython.V314.Stack.Analyze
import VeriPyAsm.CPython.V314.Stack.Soundness

/-! Atomic fused-local semantics: operand order, aliasing, failure snapshots,
and stack admission. Decoder and packed-operand tests belong to the import layer. -/

namespace VeriPyAsm.Tests.FusedSemantics

open Semantics CPython.V314 CPython.V314.Stack

theorem loadPair_order (first second : Value) (rest : List Value) :
    Command.loadPair 8 0 1 { locals := [some first, some second], stack := rest } =
      .next { pc := 8, locals := [some first, some second], stack := second :: first :: rest } := rfl

theorem loadPair_alias (value : Value) (rest : List Value) :
    Command.loadPair 8 0 0 { locals := [some value], stack := rest } =
      .next { pc := 8, locals := [some value], stack := value :: value :: rest } := rfl

theorem storeLoad_alias (value : Value) (rest : List Value) :
    Command.storeLoad 8 0 0 { locals := [none], stack := value :: rest } =
      .next { pc := 8, locals := [some value], stack := value :: rest } := rfl

theorem storePair_order (top below : Value) (rest : List Value) :
    Command.storePair 8 0 1 { locals := [none, none], stack := top :: below :: rest } =
      .next { pc := 8, locals := [some top, some below], stack := rest } := rfl

theorem storePair_alias (top below : Value) (rest : List Value) :
    Command.storePair 8 0 0 { locals := [none], stack := top :: below :: rest } =
      .next { pc := 8, locals := [some below], stack := rest } := rfl

private def entry : Frame :=
  { pc := 6, locals := [some (.int 10), some (.int 20)], stack := [.int 3, .int 2] }

example : Command.storeLoad 8 0 1 entry =
    .next { pc := 8, locals := [some (.int 3), some (.int 20)], stack := [.int 20, .int 2] } := by decide
example : Command.loadPair 8 1 0 entry =
    .next { entry with pc := 8, stack := [.int 10, .int 20, .int 3, .int 2] } := by decide
example : Command.storePair 8 1 0 entry =
    .next { pc := 8, locals := [some (.int 2), some (.int 3)] } := by decide

-- Failure snapshots preserve the entire original instruction-entry frame.
example : Command.loadPair 8 0 2 entry = .halted (.fault (.invalidLocal 2) entry) := by decide
example : Command.loadPair 8 2 0 entry = .halted (.fault (.invalidLocal 2) entry) := by decide
example : Command.loadPair 8 0 1 { entry with locals := [some (.int 10), none] } =
    .halted (.fault (.unboundUncheckedLocal 1) { entry with locals := [some (.int 10), none] }) := by decide
example : Command.loadPair 8 0 1 { entry with locals := [none, some (.int 20)] } =
    .halted (.fault (.unboundUncheckedLocal 0) { entry with locals := [none, some (.int 20)] }) := by decide
example : Command.storeLoad 8 0 2 entry = .halted (.fault (.invalidLocal 2) entry) := by decide
example : Command.storeLoad 8 2 0 entry = .halted (.fault (.invalidLocal 2) entry) := by decide
example : Command.storeLoad 8 0 1 { entry with locals := [some (.int 10), none] } =
    .halted (.fault (.unboundUncheckedLocal 1) { entry with locals := [some (.int 10), none] }) := by decide
example : Command.storePair 8 0 2 entry = .halted (.fault (.invalidLocal 2) entry) := by decide
example : Command.storePair 8 2 0 entry = .halted (.fault (.invalidLocal 2) entry) := by decide
example : Command.storeLoad 8 0 1 { entry with stack := [] } =
    .halted (.fault .stackUnderflow { entry with stack := [] }) := by decide
example : Command.storePair 8 0 1 { entry with stack := [.int 3] } =
    .halted (.fault .stackUnderflow { entry with stack := [.int 3] }) := by decide
example : Command.storePair 8 0 1 { entry with stack := [] } =
    .halted (.fault .stackUnderflow { entry with stack := [] }) := by decide

private def instruction (offset : Nat) (op : Op) : Instruction :=
  { offset, next := offset + 2, opcode := 0, arg := 0, op }

example (first second : Nat) :
    (instruction 0 (.loadFastLoadFast first second)).denote =
      (instruction 0 (.loadFastBorrowLoadFastBorrow first second)).denote := rfl

private def pairCode : Code := ⟨[
  instruction 0 (.loadFastBorrowLoadFastBorrow 0 1),
  instruction 2 (.binary .add), instruction 4 .returnValue]⟩

private def accepted (code : Code) (capacity : Nat) : Bool :=
  match analyze code capacity with
  | .ok _ => true
  | .error _ => false

private def rejection (code : Code) (capacity : Nat) : Option Stack.Error :=
  match analyze code capacity with
  | .ok _ => none
  | .error error => some error

example : accepted pairCode 2 = true := by decide
example : rejection pairCode 1 = some ⟨0, .capacityExceeded 2 1⟩ := by decide
example : rejection ⟨[instruction 0 (.storeFastLoadFast 0 1), instruction 2 .returnValue]⟩ 1 =
    some ⟨0, .underflow 1 0⟩ := by decide
example : rejection ⟨[instruction 0 (.loadSmallInt 1), instruction 2 (.storeFastStoreFast 0 1),
    instruction 4 (.jump 4)]⟩ 2 = some ⟨2, .underflow 2 1⟩ := by decide
example : accepted ⟨[instruction 0 (.loadFastLoadFast 0 1),
    instruction 2 (.storeFastStoreFast 1 0), instruction 4 (.loadSmallInt 0),
    instruction 6 .returnValue]⟩ 2 = true := by decide

#print axioms loadPair_order
#print axioms storeLoad_alias
#print axioms storePair_alias
#print axioms Stack.Certificate.run_no_underflow

end VeriPyAsm.Tests.FusedSemantics
