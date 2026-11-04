import VeriPyAsm.CPython.V314.Stack.Certificate

/-! Worklist inference of a finite height table. This algorithm is a certificate
producer; `check` independently verifies its result. Neither its traversal order
nor its fuel bound is part of the soundness argument. -/

namespace VeriPyAsm.CPython.V314.Stack

inductive ErrorReason where
  | missingInstruction
  | underflow (required actual : Nat)
  | invalidReturnHeight (actual : Nat)
  | capacityExceeded (height capacity : Nat)
  | inconsistentJoin (expected actual : Nat)
  | analysisLimit
  | invalidCertificate
  deriving Repr, DecidableEq

structure Error where
  offset : Nat
  reason : ErrorReason
  deriving Repr, DecidableEq

def Error.message (error : Error) : String :=
  let detail := match error.reason with
    | .missingInstruction => "target is not an instruction boundary"
    | .underflow required actual => s!"stack underflow: needs {required}, has {actual}"
    | .invalidReturnHeight actual => s!"return requires exactly one stack value, has {actual}"
    | .capacityExceeded height capacity =>
      s!"stack height {height} exceeds co_stacksize {capacity}"
    | .inconsistentJoin expected actual =>
      s!"inconsistent stack heights at join: {expected} and {actual}"
    | .analysisLimit => "stack analysis exhausted its work bound"
    | .invalidCertificate => "inferred stack table failed independent certificate checking"
  s!"byte offset {error.offset}: {detail}"

private def fail {α : Type} (offset : Nat) (reason : ErrorReason) : Except Error α :=
  .error ⟨offset, reason⟩

/-- Check the current instruction and propose the height on normal outgoing edges.
Python exception paths have no normal successor in this handler-free fragment. -/
private def transfer (i : Instruction) (capacity height : Nat) : Except Error Nat := do
  if i.op == .returnValue && height != 1 then
    fail i.offset (.invalidReturnHeight height)
  else if height < i.op.pops then
    fail i.offset (.underflow i.op.pops height)
  else if height > capacity then
    fail i.offset (.capacityExceeded height capacity)
  else
    let output := i.outputHeight height
    if output > capacity then fail i.offset (.capacityExceeded output capacity)
    else pure output

private def visit (code : Code) (capacity : Nat) :
    Nat → Heights → Heights → Except Error Heights
  | _, [], heights => pure heights.reverse
  | 0, (pc, _) :: _, _ => fail pc .analysisLimit
  | fuel + 1, (pc, height) :: pending, heights =>
    match heightAt heights pc with
    | some previous =>
      if previous = height then visit code capacity fuel pending heights
      else fail pc (.inconsistentJoin previous height)
    | none => do
      let some instruction := fetch code.instructions pc | fail pc .missingInstruction
      let output ← transfer instruction capacity height
      let outgoing := instruction.successors.map (fun target => (target, output))
      visit code capacity fuel (outgoing ++ pending) ((pc, height) :: heights)

/-- Infer heights starting at pc=0 with an empty operand stack. Both conditional
edges are analyzed, even if their condition is constant. Stable cycles terminate
analysis; a cycle requiring different heights is rejected. Dead instructions are
not assigned heights. Decode still checks their encoding separately. -/
def infer (code : Code) (capacity : Nat) : Except Error Heights :=
  -- Each newly visited offset enqueues its successors once. Repeated visits
  -- consume pending work but never enqueue more. The final checker is decisive
  -- even if future instruction changes make this budget too small.
  let budget := 1 + (code.instructions.map (fun i => i.successors.length)).sum
  visit code capacity budget [(0, 0)] []

/-- No table is admitted without the independently checked `Valid` proposition. -/
def analyze (code : Code) (capacity : Nat) : Except Error (Certificate code capacity) := do
  let heights ← infer code capacity
  match check code capacity heights with
  | some certificate => pure certificate
  | none => fail 0 .invalidCertificate

end VeriPyAsm.CPython.V314.Stack
