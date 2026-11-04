import VeriPyAsm.Semantics.Value

/-! Explicit one-frame execution and shallow instruction combinators. Labels are
byte offsets; the head of `stack` is its top. The stack is currently unbounded;
checking co_stacksize is a future admission obligation. Cycles live in the transition system.
Exception/fault frames are instruction-entry snapshots, not CPython unwound frames. -/

namespace VeriPyAsm.Semantics

structure Frame where
  pc : Nat := 0
  locals : List (Option Value) := []
  stack : List Value := []
  deriving Repr, DecidableEq

/-- Model failures are distinct from Python exceptions. -/
inductive Fault where
  | invalidPC (pc : Nat)
  | stackUnderflow
  | invalidLocal (index : Nat)
  | unboundUncheckedLocal (index : Nat)
  | expectedBool
  deriving Repr, DecidableEq

inductive Halt where
  | returned (value : Value) (frame : Frame)
  | raised (exception : PythonException) (frame : Frame)
  | fault (reason : Fault) (frame : Frame)
  deriving Repr, DecidableEq

inductive StepResult where
  | next (frame : Frame)
  | halted (outcome : Halt)
  deriving Repr, DecidableEq

/-- A shallow instruction is a Lean function, not another instruction AST. -/
abbrev Command := Frame → StepResult
abbrev Program := Nat → Option Command

namespace Command

def jump (target : Nat) : Command := fun s => .next { s with pc := target }

def push (next : Nat) (value : Value) : Command := fun s =>
  .next { s with pc := next, stack := value :: s.stack }

def load (checked : Bool) (next index : Nat) : Command := fun s =>
  match s.locals[index]? with
  | none => .halted (.fault (.invalidLocal index) s)
  | some none =>
    if checked then .halted (.raised .unboundLocalError s)
    else .halted (.fault (.unboundUncheckedLocal index) s)
  | some (some value) => push next value s

def store (next index : Nat) : Command := fun s =>
  if index ≥ s.locals.length then .halted (.fault (.invalidLocal index) s)
  else match s.stack with
    | [] => .halted (.fault .stackUnderflow s)
    | value :: rest => .next
        { s with pc := next, locals := s.locals.set index (some value), stack := rest }

def binary (next : Nat) (operation : Value → Value → Except PythonException Value) :
    Command := fun s =>
  match s.stack with
  | right :: left :: rest => match operation left right with
    | .ok value => .next { s with pc := next, stack := value :: rest }
    | .error exception => .halted (.raised exception s)
  | _ => .halted (.fault .stackUnderflow s)

def toBool (next : Nat) : Command := fun s =>
  match s.stack with
  | value :: rest => .next { s with pc := next, stack := .bool value.truthy :: rest }
  | [] => .halted (.fault .stackUnderflow s)

/-- CPython 3.14 POP_JUMP_IF_* requires an exact bool; TO_BOOL is separate. -/
def branch (ifTrue ifFalse : Nat) : Command := fun s =>
  match s.stack with
  | .bool b :: rest => .next
      { s with pc := if b then ifTrue else ifFalse, stack := rest }
  | [] => .halted (.fault .stackUnderflow s)
  | _ => .halted (.fault .expectedBool s)

def ret : Command := fun s =>
  match s.stack with
  | value :: rest => .halted (.returned value { s with stack := rest })
  | [] => .halted (.fault .stackUnderflow s)

end Command

def step (program : Program) (frame : Frame) : StepResult :=
  match program frame.pc with
  | some command => command frame
  | none => .halted (.fault (.invalidPC frame.pc) frame)

/-- One transition, including terminal and failing transitions. -/
def Transition (next : Frame → StepResult) (s : Frame) (result : StepResult) : Prop :=
  next s = result

theorem transition_deterministic (next : Frame → StepResult) (s : Frame)
    (a b : StepResult) (ha : Transition next s a) (hb : Transition next s b) : a = b :=
  ha.symm.trans hb

inductive RunResult where
  | halted (outcome : Halt)
  | exhausted (frame : Frame)
  deriving Repr, DecidableEq

/-- Fuel exhaustion is inconclusive, not a Python exception or a termination proof. -/
def run (next : Frame → StepResult) : Nat → Frame → RunResult
  | 0, s => .exhausted s
  | fuel + 1, s => match next s with
    | .halted outcome => .halted outcome
    | .next s' => run next fuel s'

end VeriPyAsm.Semantics
