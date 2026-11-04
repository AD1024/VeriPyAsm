import VeriPyAsm.CPython.V314.Language

/-! Stack requirements for the current atomic instructions. Required operands
are separate from the net effect: e.g. TO_BOOL requires one item despite delta 0.
Future fused instructions must also account for any intermediate peak height. -/

namespace VeriPyAsm.CPython.V314

def Op.pops : Op → Nat
  | .storeFast _ | .toBool | .popJumpIfFalse .. | .popJumpIfTrue .. | .returnValue => 1
  | .binary _ | .compare _ => 2
  | .resume | .notTaken | .loadConst _ | .loadSmallInt _ | .loadFast _ |
      .loadFastBorrow _ | .loadFastCheck _ | .jump _ => 0

def Op.pushes : Op → Nat
  | .loadConst _ | .loadSmallInt _ | .loadFast _ | .loadFastBorrow _ |
      .loadFastCheck _ | .binary _ | .compare _ | .toBool => 1
  | .resume | .notTaken | .storeFast _ | .jump _ | .popJumpIfFalse .. |
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
