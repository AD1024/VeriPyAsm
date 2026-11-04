import VeriPyAsm.CPython.V314.Language

/-! Stack requirements for the current atomic instructions. Required operands
are separate from the net effect: e.g. TO_BOOL requires one item despite delta 0.
The implemented fused locals never exceed the larger endpoint height; see
Semantics/Fused.lean. Future fusions must account for intermediate peaks too. -/

namespace VeriPyAsm.CPython.V314

def Op.pops : Op → Nat
  | .storeFast _ | .storeFastLoadFast .. | .toBool | .popJumpIfFalse .. |
      .popJumpIfTrue .. | .returnValue => 1
  | .binary _ | .compare _ | .storeFastStoreFast .. => 2
  | .resume | .notTaken | .loadConst _ | .loadSmallInt _ | .loadFast _ |
      .loadFastBorrow _ | .loadFastCheck _ | .loadFastLoadFast .. |
      .loadFastBorrowLoadFastBorrow .. | .jump _ => 0

def Op.pushes : Op → Nat
  | .loadConst _ | .loadSmallInt _ | .loadFast _ | .loadFastBorrow _ |
      .loadFastCheck _ | .storeFastLoadFast .. | .binary _ | .compare _ | .toBool => 1
  | .loadFastLoadFast .. | .loadFastBorrowLoadFastBorrow .. => 2
  | .resume | .notTaken | .storeFast _ | .storeFastStoreFast .. | .jump _ | .popJumpIfFalse .. |
      .popJumpIfTrue .. | .returnValue => 0

/-- Return consumes the entire frame's operand stack in this admission profile. -/
def Instruction.StackReady (i : Instruction) (height : Nat) : Prop :=
  i.op.pops ≤ height ∧ (i.op = .returnValue → height = 1)

instance (i : Instruction) (height : Nat) : Decidable (i.StackReady height) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Used only after StackReady rules out truncated subtraction. -/
def Instruction.outputHeight (i : Instruction) (height : Nat) : Nat :=
  height - i.op.pops + i.op.pushes

end VeriPyAsm.CPython.V314
