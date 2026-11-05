import VeriPyAsm.Verification.AxiomAudit

/-! Evidence policy shared by manual registration and automated discharge.
The default audit stays strict. Solver trust must be explicitly selected and
permits exactly one additional axiom, never `sorryAx` or native-decision trust. -/

namespace VeriPyAsm.Verification.VC

open Lean

/-- Check synchronously before using Lean's declaration API, whose error recovery
can otherwise insert an axiom for an ill-typed declaration. Failed attempts leave
the environment intact; successful declarations are checked again on insertion. -/
def addCheckedDeclaration (declaration : Declaration) : CoreM Unit := do
  let environment ← getEnv
  let options := (← getOptions).setBool `debug.skipKernelTC false |>.setBool `Elab.async false
  discard <| ofExceptKernelException <| environment.addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize declaration
    (← read).cancelTk?
  try
    withOptions (fun _ => options) <| addDecl declaration
  catch error =>
    setEnv environment
    throw error

inductive Policy where
  | checked
  | solver_trusted
  deriving BEq, Repr, Inhabited

instance : ToString Policy where
  toString
    | .checked => "checked"
    | .solver_trusted => "solver_trusted"

def Policy.parse (value : String) : Except String Policy :=
  match value with
  | "checked" => .ok .checked
  | "solver_trusted" => .ok .solver_trusted
  | _ => .error s!"unknown verification policy {value}; expected checked or solver_trusted"

def Policy.permits (policy : Policy) (name : Name) : Bool :=
  AxiomAudit.approved.contains name || (policy == .solver_trusted && name == `Crush.crushSorry)

/-- Inspect the actual transitive dependencies, including the statement. The
returned list determines assurance; selecting solver trust does not lower the
assurance of a proof which only uses standard Lean axioms. -/
def audit (name : Name) (policy : Policy := .checked) : CoreM (Array Name) := do
  let some info := (← getEnv).checked.get.find? name
    | throwError "VC audit: no kernel-checked declaration {name}"
  if info.isUnsafe || info.isPartial then
    throwError "VC audit: {name} is not a safe kernel declaration"
  let axioms := (← collectAxioms name).qsort Name.quickLt
  let unexpected := axioms.filter (fun axiomName => !policy.permits axiomName)
  unless unexpected.isEmpty do
    throwError "VC audit ({policy}): {name} depends on unapproved axioms {unexpected.toList}"
  return axioms

def assurance (axioms : Array Name) : Policy :=
  if axioms.contains `Crush.crushSorry then .solver_trusted else .checked

end VeriPyAsm.Verification.VC
