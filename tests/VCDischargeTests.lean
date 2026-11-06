import VeriPyAsm.Examples.Triangular.Manifest
import VeriPyAsm.Examples.Triangular.Arithmetic
import VeriPyAsm.Verification.VC.Discharge

namespace VeriPyAsm.Tests.VCDischarge

open Lean Meta Elab Command Verification
open Examples Examples.Triangular

-- Discovery emits complete statements but no unconditional artifact package.
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from obligations

example : pending.report.complete = false := rfl
example : pending.report.obligations.size = 4 := rfl
example : pending.report.finalDeclaration = none := rfl

#eval show CoreM Unit from do
  if (← getEnv).contains `VeriPyAsm.Tests.VCDischarge.pending then
    throwError "discovery exported an unconditional result"

-- Each emitted statement parses back to exactly the original closed VC.
run_cmd liftTermElabM do
  let manifest ← Verification.VC.getManifest ``obligations
  for obligation in manifest.obligations do
    let text ← Verification.VC.goalStatement obligation.goal
    let .ok termSyntax := Parser.runParserCategory (← getEnv) `term text
      | throwError "unparseable VC statement: {text}"
    let expression ← Term.elabType termSyntax
    Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    unless !expression.hasMVar && !expression.hasFVar &&
        (← isDefEq expression (mkConst obligation.goal)) do
      throwError "emitted statement changed the VC"

@[veripy_proof VC.loop6.init]
theorem init : VC.loop6.init := Arithmetic.at_entry
@[veripy_proof VC.loop6.preserve]
theorem preserve : VC.loop6.preserve := Arithmetic.preserve
@[veripy_proof VC.loop6.exit]
theorem exit : VC.loop6.exit := Arithmetic.exit

-- Strict failure rolls back even the successful per-VC declarations.
/-- error: verification incomplete: 1 unresolved VC(s); no VerifiedArtifact exported -/
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify incomplete from obligations

#eval show CoreM Unit from do
  for name in [`VeriPyAsm.Tests.VCDischarge.incomplete,
      `VeriPyAsm.Tests.VCDischarge.incomplete.vc.init,
      `VeriPyAsm.Tests.VCDischarge.incomplete.report] do
    if (← getEnv).contains name then throwError "incomplete strict run exported {name}"

@[veripy_proof VC.loop6.decrease]
theorem decrease : VC.loop6.decrease := Arithmetic.decrease

#guard_msgs (drop info, all) in
veripy_verify verified from obligations with
  VC.loop6.exit (backend := "z3") (timeout := 2) (policy := "solver_trusted")

example : Nonempty (VerifiedArtifact triangularArtifact triangularContract) := ⟨verified⟩
example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[2]!.configuredBackend = "z3" := rfl
example : verified.report.obligations[2]!.timeoutSeconds = 2 := rfl
example : verified.report.obligations[2]!.policy = "solver_trusted" := rfl
example : verified.report.obligations[2]!.actualBackend = none := rfl
example : verified.report.obligations[2]!.provider = "manual" := rfl

-- Final packages support compiled consumers, including execution of the
-- admitted program. Merely checking the package's type does not test this.
def copiedPackage : VerifiedArtifact triangularArtifact triangularContract := verified

#eval show IO Unit from do
  let observed := Semantics.run (Semantics.step copiedPackage.admission.translation.program) 100
    { locals := [some (.int 3), none] }
  unless observed = .halted (.returned (.int 6)
      { pc := 60, locals := [some (.int 0), some (.int 6)] }) do
    throw <| IO.userError "compiled verification package executed incorrectly"

-- Explicitly noncomputable user assemblies remain valid proof evidence. Their
-- packages preserve Lean's noncomputable marker rather than claiming execution.
noncomputable def choiceAssembly (proofs : VC.Proofs) :
    VerifiedArtifact triangularArtifact triangularContract :=
  Classical.choice ⟨Assembly.verified proofs⟩

veripy_vcs choiceGoals : VerifiedArtifact triangularArtifact triangularContract via choiceAssembly where
  init : VC.loop6.init at 6 vc_kind "initialization"
  preserve : VC.loop6.preserve at 6 vc_kind "preservation"
  exit : VC.loop6.exit at 58 vc_kind "normal_exit"
  decrease : VC.loop6.decrease at 6 vc_kind "ranking"

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify choicePackage from choiceGoals

example : Nonempty (VerifiedArtifact triangularArtifact triangularContract) := ⟨choicePackage⟩

#eval show CoreM Unit from do
  unless isNoncomputable (← getEnv) ``choicePackage do
    throwError "noncomputable assembly lost its marker"

-- The JSON is valid and contains the full report; the command can emit it too.
#eval show IO Unit from do
  let .ok json := Json.parse verified.report.json | throw <| IO.userError "invalid report JSON"
  let .ok (_ : Verification.VC.Report) := fromJson? json
    | throw <| IO.userError "report schema did not round trip"

#guard_msgs (drop info, all) in
#veripy_report verified.report

/-- error: list every VC structure field exactly once -/
#guard_msgs in
veripy_vcs missing : VerifiedArtifact triangularArtifact triangularContract
    via Assembly.verified where
  init : VC.loop6.init at 6 vc_kind "initialization"

/-- error: VC assembly must produce a VerifiedArtifact package -/
#guard_msgs in
veripy_vcs lowerLevel : ArtifactTotalCorrect triangularArtifact triangularContract
    via Assembly.artifact_total where
  init : VC.loop6.init at 6 vc_kind "initialization"

/-- error: unknown verification policy reconstructOrTrust; expected checked or solver_trusted -/
#guard_msgs in
set_option veripy.policy "reconstructOrTrust" in
veripy_verify badPolicy from obligations

-- Fingerprints include metadata, the VC expressions, and transitive dependencies.
#eval show CoreM Unit from do
  let manifest ← Verification.VC.getManifest ``obligations
  let original ← Verification.VC.fingerprint manifest
  let changed := { manifest with
    obligations := manifest.obligations.modify 0 (fun obligation => { obligation with offset := 2 }) }
  if (← Verification.VC.fingerprint changed) == original then
    throwError "changed metadata did not change fingerprint"

def rejectedGoal : Prop := False
def acceptedGoal : Prop := True

structure UntrustedProofs : Prop where
  bad : rejectedGoal
  good : acceptedGoal

def untrustedAssembly (_proofs : UntrustedProofs) :
    VerifiedArtifact triangularArtifact triangularContract := Assembly.verified Arithmetic.proofs

veripy_vcs untrusted : VerifiedArtifact triangularArtifact triangularContract via untrustedAssembly where
  bad : rejectedGoal at 0 vc_kind "invalid_backend_evidence"
  good : acceptedGoal at 2 vc_kind "valid_backend_evidence"

-- A backend is an untrusted proof producer. Even a success response with an
-- ill-typed expression must not insert Lean's recovery axiom, taint the next VC,
-- or retain auxiliary declarations from the failed attempt.
#guard_msgs (drop info, all) in
run_cmd do
  let environment ← getEnv
  let previous ← Verification.VC.solverRef.get
  try
    Verification.VC.solverRef.set <| some fun _ goal => do
      if goal.isConstOf ``rejectedGoal then
        Verification.VC.addCheckedDeclaration (.thmDecl {
          name := `BackendFixture.auxiliary, levelParams := [],
          type := mkConst ``True, value := mkConst ``True.intro })
      return { proof := some (mkConst ``True.intro) }
    let manifest ← liftCoreM <| Verification.VC.getManifest ``untrusted
    let report ← Verification.VC.runManifest manifest `BackendFixture.run false {}
    unless report.obligations[0]!.failureKind == some "invalid_evidence" &&
        report.obligations[1]!.status == "proved" do
      throwError "backend evidence was not independently checked"
    for name in [`BackendFixture.auxiliary, `BackendFixture.run.vc.bad, `BackendFixture.run] do
      if (← getEnv).contains name then throwError "failed backend attempt exported {name}"
  finally
    Verification.VC.solverRef.set previous
    setEnv environment

#veripy_audit VeriPyAsm.Tests.VCDischarge

end VeriPyAsm.Tests.VCDischarge
