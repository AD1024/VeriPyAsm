import VeriPyAsm.Verification.VC.Report

register_option veripy.policy : String := {
  defValue := "checked", descr := "VC evidence policy: checked or solver_trusted"
}
register_option veripy.backend : String := {
  defValue := "cvc5", descr := "SMT backend used by the optional Crush adapter"
}
register_option veripy.timeout : Nat := {
  defValue := 5, descr := "Per-query solver timeout in seconds"
}
register_option veripy.auto : Bool := {
  defValue := true, descr := "Try Crush after registered VC proofs"
}

namespace VeriPyAsm.Verification.VC

open Lean Elab

structure Config where
  policy : Policy := .checked
  backend : String := "cvc5"
  timeout : Nat := 5
  auto : Bool := true
  deriving Inhabited

def Config.ofOptions (options : Options) : CoreM Config := do
  let policy ← match Policy.parse (veripy.policy.get options) with
    | .ok value => pure value
    | .error message => throwError message
  let backend := veripy.backend.get options
  unless ["cvc5", "z3", "bitwuzla"].contains backend do
    throwError "unknown verification backend {backend}; expected cvc5, z3, or bitwuzla"
  let timeout := veripy.timeout.get options
  if timeout == 0 then throwError "veripy.timeout must be positive"
  return { policy, backend, timeout, auto := veripy.auto.get options }

structure Attempt where
  proof : Option Expr := none
  failureKind : String := "automation_failed"
  detail : String := ""
  actualBackend : Option String := none
  path : Option String := none
  events : Array String := #[]

abbrev Solver := Config → Expr → TermElabM Attempt

/-- The core does not import Crush. The optional adapter installs this callback
during module initialization. Its output is untrusted until the core checks it. -/
initialize solverRef : IO.Ref (Option Solver) ← IO.mkRef none

def installSolver (solver : Solver) : IO Unit := do
  unless ← initializing do throw <| IO.userError "VC solver installation requires module initialization"
  if (← solverRef.get).isSome then throw <| IO.userError "VC solver already installed"
  solverRef.set (some solver)

end VeriPyAsm.Verification.VC
