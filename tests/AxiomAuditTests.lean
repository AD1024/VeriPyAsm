import VeriPyAsm.Verification.AxiomAudit
import VeriPyAsm.Examples.Add1

/-! Negative audit fixtures exist only in a restored temporary environment.
No admitted theorem or nonstandard axiom is exported by this test module. -/

namespace VeriPyAsm.Tests.AxiomAudit

open Lean Verification.AxiomAudit

structure ProofContainer where
  checked : True

private def expectRejection (action : CoreM Unit) (reason : String) : CoreM Unit := do
  let failure ← try action; pure none catch error => pure (some error)
  let some error := failure | throwError "expected the axiom audit to reject this fixture"
  let message ← error.toMessageData.toString
  unless message.contains reason do
    throwError "unexpected audit failure: {message}"

/-- warning: declaration uses `sorry` -/
#guard_msgs in
#eval show CoreM Unit from do
  checkDeclaration ``Examples.add1_verified
  checkDeclaration ``Examples.add1Admitted
  withoutModifyingEnv do
    addDecl (.axiomDecl {
      name := `AuditFixture.assumption
      levelParams := []
      type := mkConst ``True
      isUnsafe := false })
    addDecl (.thmDecl {
      name := `AuditFixture.indirect
      levelParams := []
      type := mkConst ``True
      value := mkConst `AuditFixture.assumption })
    addDecl (.defnDecl {
      name := `AuditFixture.certificate
      levelParams := []
      type := mkConst ``ProofContainer
      value := mkApp (mkConst ``ProofContainer.mk) (mkConst `AuditFixture.indirect)
      hints := .abbrev
      safety := .safe })
    for name in [`AuditFixture.assumption, `AuditFixture.indirect, `AuditFixture.certificate] do
      expectRejection (checkDeclaration name) "AuditFixture.assumption"
    expectRejection (discard <| checkNamespace `AuditFixture) "AuditFixture.assumption"
    addDecl (.thmDecl {
      name := `AuditFixture.admitted
      levelParams := []
      type := mkConst ``True
      value := mkApp2 (mkConst ``sorryAx [.zero]) (mkConst ``True) (mkConst ``Bool.false) })
    expectRejection (checkDeclaration `AuditFixture.admitted) "sorryAx"
  if (← getEnv).contains `AuditFixture.assumption then
    throwError "negative audit fixture escaped its temporary environment"
  expectRejection (checkDeclaration `AuditFixture.missing) "no kernel-checked declaration"
  expectRejection (discard <| checkNamespace `MissingAuditNamespace) "no declarations"

example : approved.contains `Crush.crushSorry = false := by decide
example : approved.contains `Lean.ofReduceBool = false := by decide

#veripy_audit VeriPyAsm.Tests.AxiomAudit

end VeriPyAsm.Tests.AxiomAudit
