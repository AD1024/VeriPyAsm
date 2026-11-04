/-! Exact scalar values for the first bytecode slice. No Python object identity,
subclasses, allocation failure, or overloaded operations are modeled here. -/

namespace VeriPyAsm.Semantics

inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | none
  deriving Repr, DecidableEq

inductive PythonException where
  | typeError
  | unboundLocalError
  deriving Repr, DecidableEq

inductive BinaryOp where
  | add | sub | mul
  deriving Repr, DecidableEq

inductive CompareOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq

/-- Booleans participate in arithmetic as 0 and 1, but retain their value tag. -/
def Value.asInt : Value → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | .none => Option.none

def Value.truthy : Value → Bool
  | .int n => n != 0
  | .bool b => b
  | .none => false

/-- Python equality differs from equality of the tagged Lean representation. -/
def Value.pythonEq (left right : Value) : Bool :=
  match left.asInt, right.asInt with
  | some a, some b => a == b
  | _, _ => match left, right with
    | .none, .none => true
    | _, _ => false

def binary (op : BinaryOp) (left right : Value) : Except PythonException Value :=
  match left.asInt, right.asInt with
  | some a, some b => .ok (.int (match op with
    | .add => a + b
    | .sub => a - b
    | .mul => a * b))
  | _, _ => .error .typeError

def compare (op : CompareOp) (left right : Value) : Except PythonException Value :=
  match op with
  | .eq => .ok (.bool (left.pythonEq right))
  | .ne => .ok (.bool (!(left.pythonEq right)))
  | _ => match left.asInt, right.asInt with
    | some a, some b => .ok (.bool (match op with
      | .lt => a < b
      | .le => a ≤ b
      | .gt => a > b
      | .ge => a ≥ b
      | _ => false))
    | _, _ => .error .typeError

end VeriPyAsm.Semantics
