import VCRegistryTests.Provider
import VeriPyAsm.Examples.Triangular.VC
import VeriPyAsm.Examples.Triangular.Arithmetic

namespace VeriPyAsm.Tests.VCRegistry

open Lean Verification.VC

def triangleGoal : Prop := Examples.Triangular.VC.loop6.preserve

@[veripy_proof triangleGoal]
theorem triangle : ∀ N n sum : Int, 2 * sum + n * (n + 1) = N * (N + 1) →
    2 * (sum + n) + (n - 1) * ((n - 1) + 1) = N * (N + 1) :=
  Examples.Triangular.Arithmetic.preserve

-- The emitted certificate really is an equality of the complete statements.
example : (∀ n : Int, 0 ≤ n → n + 1 > n) = Fixture.goal := Fixture.supplied.veripy_match

def reordered : Prop := ∀ n : Int, n + 1 > n ∧ 0 ≤ n
def conjunction : Prop := ∀ n : Int, 0 ≤ n → 0 ≤ n ∧ n + 1 > n
def changed : Prop := ∀ n : Int, 0 ≤ n → n + 2 > n
def instanceGoal : Prop := 1 + (1 : Int) > 1

theorem general (n : Int) : n + 1 > n := by omega
theorem instanceProof : 1 + (1 : Int) > 1 := by omega
theorem swapped (n : Int) (h : 0 ≤ n) : n + 1 > n ∧ 0 ≤ n := ⟨by omega, h⟩

private def rejects (action : CoreM Unit) (reason : String) : CoreM Unit := do
  let failure ← try action; pure none catch error => pure (some error)
  let some error := failure | throwError "expected rejection: {reason}"
  unless (← error.toMessageData.toString).contains reason do
    throwError "unexpected rejection: {error.toMessageData}"

#eval show CoreM Unit from do
  -- Registration and its certificate survive an actual module import.
  unless (← registeredProof? ``Fixture.goal) == some ``Fixture.supplied do
    throwError "imported registration missing"
  withoutModifyingEnv do
    let some (name, axioms) ← resolveRegistered ``Fixture.goal `RegistryFixture.imported
      | throwError "imported proof not resolved"
    unless name == ``Fixture.supplied && assurance axioms == .checked do
      throwError "incorrect imported evidence"
    rejects (registerProof ``Fixture.supplied ``Fixture.goal) "duplicate VC registration"
    -- No implicit specialization, removal of hypotheses, equivalence, or stale statement reuse.
    rejects (certifyExact `RegistryFixture.a ``general ``Fixture.goal) "must match by rfl"
    rejects (certifyExact `RegistryFixture.b ``general ``instanceGoal) "must match by rfl"
    rejects (certifyExact `RegistryFixture.c ``swapped ``conjunction) "must match by rfl"
    rejects (certifyExact `RegistryFixture.d ``Fixture.supplied ``changed) "must match by rfl"
    rejects (certifyExact `RegistryFixture.e ``instanceProof ``Fixture.goal) "must match by rfl"
    rejects (discard <| goalExpr ``Fixture.supplied) "proposition definition"
    rejects (discard <| goalExpr ``Int) "proposition definition"
    -- Simulate independent imported entries: resolution must preserve ambiguity.
    modifyEnv fun env => registry.addEntry env (``Fixture.goal, ``general)
    rejects (discard <| registeredProof? ``Fixture.goal) "ambiguous VC proofs"

-- Trust selection never permits arbitrary axioms, sorry, or native-decision trust.
example : Policy.checked.permits `Crush.crushSorry = false := rfl
example : Policy.solver_trusted.permits `Crush.crushSorry = true := rfl
example : Policy.solver_trusted.permits `sorryAx = false := rfl
example : Policy.solver_trusted.permits `Lean.ofReduceBool = false := rfl

/-- warning: declaration uses `sorry` -/
#guard_msgs in
#eval show CoreM Unit from do
  withoutModifyingEnv do
    addDecl (.axiomDecl {
      name := `RegistryFixture.assumption, levelParams := [],
      type := mkConst ``True, isUnsafe := false })
    addDecl (.thmDecl {
      name := `RegistryFixture.indirect, levelParams := [],
      type := mkConst ``True, value := mkConst `RegistryFixture.assumption })
    for policy in [Policy.checked, .solver_trusted] do
      rejects (discard <| audit `RegistryFixture.indirect policy) "RegistryFixture.assumption"
    addDecl (.thmDecl {
      name := `RegistryFixture.admitted, levelParams := [],
      type := mkConst ``True,
      value := mkApp2 (mkConst ``sorryAx [.zero]) (mkConst ``True) (mkConst ``Bool.false) })
    for policy in [Policy.checked, .solver_trusted] do
      rejects (discard <| audit `RegistryFixture.admitted policy) "sorryAx"

#veripy_audit VeriPyAsm.Tests.VCRegistry

end VeriPyAsm.Tests.VCRegistry
