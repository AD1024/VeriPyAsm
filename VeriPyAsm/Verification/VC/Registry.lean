import VeriPyAsm.Verification.VC.Policy

/-! Exact, persistent registration of user proofs of closed named VCs.
The index only locates a candidate. Every use rechecks the full theorem type
by a kernel-checked `Eq.refl` certificate and audits its transitive dependencies.
No theorem application, unification with arguments, or logical rewriting is used.
-/

namespace VeriPyAsm.Verification.VC

open Lean

private def insertRegistration (state : NameMap (Array Name)) (entry : Name × Name) :=
  state.insert entry.1 ((state.find? entry.1 |>.getD #[]).push entry.2)

initialize registry : SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := insertRegistration
    addImportedFn := fun entries =>
      entries.foldl (fun state moduleEntries => moduleEntries.foldl insertRegistration state) {}
  }

/-- Only closed proposition definitions are obligations. Universe-polymorphic
schemas must first be wrapped in a closed VC definition by the generator. -/
def goalExpr (name : Name) : CoreM Expr := do
  let some (.defnInfo info) := (← getEnv).checked.get.find? name
    | throwError "VC {name} must be a kernel-checked proposition definition"
  unless info.type == mkSort .zero && info.levelParams.isEmpty &&
      !info.value.hasMVar && !info.value.hasFVar do
    throwError "VC {name} must be a closed proposition definition without universe parameters"
  return mkConst name

/-- Construct exactly `show T = G from rfl` and submit it to the kernel. The
certificate is reusable evidence, not a boolean from a meta-level matcher. -/
def certifyExact (certificate theoremName goalName : Name) : CoreM Unit := do
  let goal ← goalExpr goalName
  let some (.thmInfo info) := (← getEnv).checked.get.find? theoremName
    | throwError "VC proof {theoremName} must be a kernel-checked theorem"
  unless info.levelParams.isEmpty && !info.type.hasMVar && !info.type.hasFVar do
    throwError "VC proof {theoremName} must have a closed type without universe parameters"
  let type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero) info.type goal
  let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkSort .zero) info.type
  try
    addCheckedDeclaration (.thmDecl { name := certificate, levelParams := [], type, value })
  catch _ =>
    throwError "VC proof {theoremName} does not match {goalName}: the complete theorem type must match by rfl"

/-- Preserve ambiguity across imports instead of choosing a proof according to
import order. Duplicate independent registrations are rejected at lookup. -/
def registeredProof? (goalName : Name) : CoreM (Option Name) := do
  match registry.getState (← getEnv) |>.find? goalName |>.getD #[] with
  | #[] => return none
  | #[name] => return some name
  | names => throwError "ambiguous VC proofs for {goalName}: {names.toList}"

def registerProof (theoremName goalName : Name) (policy : Policy := .checked) : CoreM Unit := do
  if let some previous ← registeredProof? goalName then
    throwError "duplicate VC registration for {goalName}: already registered {previous}"
  discard <| audit theoremName policy
  certifyExact (theoremName ++ `veripy_match) theoremName goalName
  modifyEnv fun env => registry.addEntry env (goalName, theoremName)

/-- Revalidate on every use, including imports and different trust policies.
There is no proof cache keyed solely by a human-readable obligation name. -/
def resolveRegistered (goalName certificate : Name) (policy : Policy := .checked) :
    CoreM (Option (Name × Array Name)) := do
  let some theoremName ← registeredProof? goalName | return none
  let axioms ← audit theoremName policy
  certifyExact certificate theoremName goalName
  return some (theoremName, axioms)

syntax (name := veripy_proof) "veripy_proof " ident (" solver_trusted")? : attr

initialize registerBuiltinAttribute {
  name := `veripy_proof
  descr := "Register an exact, axiom-audited proof of a named VeriPyAsm VC"
  applicationTime := .afterCompilation
  add := fun name stx kind => do
    unless kind == .global do
      throwError "veripy_proof only supports global registrations"
    let target ← Elab.realizeGlobalConstNoOverloadWithInfo stx[1]
    let policy := if stx[2].isNone then Policy.checked else .solver_trusted
    registerProof name target policy
}

end VeriPyAsm.Verification.VC
