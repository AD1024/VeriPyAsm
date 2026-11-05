import VeriPyAsm.CPython.V314.Ownership.Certificate

/-! An untrusted worklist proposes ownership tables. The separate decidable
certificate checker must accept the complete table before admission. -/

namespace VeriPyAsm.CPython.V314.Ownership

inductive ErrorReason where
  | missingInstruction
  | violation (reason : Violation)
  | inconsistentJoin
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
    | .violation reason => reason.message
    | .inconsistentJoin => "inconsistent ownership at join"
    | .analysisLimit => "ownership analysis exhausted its work bound"
    | .invalidCertificate => "inferred ownership table failed independent checking"
  s!"byte offset {error.offset}: {detail}"

private def fail {α : Type} (offset : Nat) (reason : ErrorReason) : Except Error α :=
  .error ⟨offset, reason⟩

private def visit (code : Code) : Nat → Table → Table → Except Error Table
  | _, [], table => pure table.reverse
  | 0, (pc, _) :: _, _ => fail pc .analysisLimit
  | fuel + 1, (pc, refs) :: pending, table =>
    match stackAt table pc with
    | some previous =>
      if previous = refs then visit code fuel pending table
      else fail pc .inconsistentJoin
    | none => do
      let some instruction := fetch code.instructions pc | fail pc .missingInstruction
      let output ← (transfer instruction.op refs).mapError (fun v => ⟨pc, .violation v⟩)
      let outgoing := instruction.successors.map (fun target => (target, output))
      visit code fuel (outgoing ++ pending) ((pc, refs) :: table)

def infer (code : Code) : Except Error Table :=
  let budget := 1 + (code.instructions.map (fun i => i.successors.length)).sum
  visit code budget [(0, [])] []

def analyze (code : Code) : Except Error (Certificate code) := do
  let table ← infer code
  match check code table with
  | some certificate => pure certificate
  | none => fail 0 .invalidCertificate

end VeriPyAsm.CPython.V314.Ownership
