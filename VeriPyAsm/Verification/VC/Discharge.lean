import VeriPyAsm.Verification.VC.Backend

/-! Registered proofs first, optional automation second, audited assembly last.
Discovery may publish proved VCs and a report. Strict verification publishes a
VerifiedArtifact only when all obligations and the final package pass policy.
No failed proof attempt or incomplete strict run exports an admitted declaration.
-/

register_option veripy.json : Bool := {
  defValue := false, descr := "Also emit the complete VC report as JSON in diagnostics"
}

namespace VeriPyAsm.Verification.VC

open Lean Meta Elab Command

private def dischargeOne (runName : Name) (obligation : Obligation) (config : Config) :
    TermElabM (Option Expr × ObligationReport) := do
  let environment ← getEnv
  let started ← IO.monoMsNow
  let theoremName := runName ++ `vc ++ obligation.field
  -- References retain diagnostic events if a later stage throws. Pure mutable
  -- locals inside `try` would roll back their updates on the exception path.
  let reportRef ← IO.mkRef ({
    goal := obligation.goal.toString, offset := obligation.offset, kind := obligation.kind,
    source := obligation.source, context := ← goalContext obligation.goal,
    dependencies := obligation.dependencies.map Name.toString,
    dependencyScope := obligation.dependencyScope,
    statement := ← goalStatement obligation.goal, status := "pending", policy := toString config.policy,
    configuredBackend := config.backend, timeoutSeconds := config.timeout } : ObligationReport)
  let stageRef ← IO.mkRef "registration_rejected"
  try
    let proof ← if let some name ← registeredProof? obligation.goal then do
      reportRef.modify fun report => { report with provider := "manual", theoremName := some name.toString }
      discard <| resolveRegistered obligation.goal (runName ++ `matches ++ obligation.field) config.policy
      pure (mkConst name)
    else do
      stageRef.set "no_registered_proof"
      unless config.auto do throwError "automation disabled; no registered proof"
      stageRef.set "backend_unavailable"
      let some solver ← solverRef.get
        | throwError "Crush adapter unavailable; import VeriPyAsm.Automation.Crush or supply a registered proof"
      reportRef.modify fun report => { report with provider := "crush" }
      stageRef.set "automation_failed"
      let attempt ← solver config (← goalExpr obligation.goal)
      reportRef.modify fun report => { report with
        actualBackend := attempt.actualBackend, path := attempt.path, events := attempt.events }
      stageRef.set attempt.failureKind
      let some proof := attempt.proof | throwError attempt.detail
      pure proof
    stageRef.set "invalid_evidence"
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasFVar || proof.hasSorry then
      throwError "VC proof contains unresolved variables or sorry"
    addCheckedDeclaration (.thmDecl {
      name := theoremName, levelParams := [], type := ← goalExpr obligation.goal, value := proof })
    stageRef.set "policy_rejected"
    let axioms ← audit theoremName config.policy
    let report ← reportRef.get
    return (some (mkConst theoremName), { report with
      status := "proved", assurance := some (toString (assurance axioms)),
      axioms := axioms.map Name.toString, elapsedMs := (← IO.monoMsNow) - started,
      theoremName := report.theoremName.or (some theoremName.toString) })
  catch error =>
    setEnv environment
    let report ← reportRef.get
    return (none, { report with
      failureKind := some (← stageRef.get), detail := ← error.toMessageData.toString,
      elapsedMs := (← IO.monoMsNow) - started })

syntax vcOverride := ident (" (" &"backend" " := " str ")")?
  (" (" &"timeout" " := " num ")")? (" (" &"policy" " := " str ")")?
syntax (name := discoverCommand) "veripy_discover " ident " from " ident
  (" with " ppLine (colGt vcOverride ppLine)+)? : command
syntax (name := verifyCommand) "veripy_verify " ident " from " ident
  (" with " ppLine (colGt vcOverride ppLine)+)? : command

private def overrides (manifest : Manifest) (stxs : Array (TSyntax ``vcOverride))
    (base : Config) : CommandElabM (NameMap Config) := do
  let mut configs := {}
  for stx in stxs do
    let `(vcOverride| $goalId:ident $[(backend := $backend:str)]?
        $[(timeout := $timeout:num)]? $[(policy := $policy:str)]?) := stx
      | throwUnsupportedSyntax
    let goal ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo goalId
    unless manifest.obligations.any (·.goal == goal) do
      throwErrorAt goalId "override does not name an obligation in this manifest"
    if configs.contains goal then throwErrorAt goalId "duplicate VC override"
    let options := (← getOptions)
      |>.set `veripy.backend (backend.map (·.getString) |>.getD base.backend)
      |>.set `veripy.timeout (timeout.map (·.getNat) |>.getD base.timeout)
      |>.set `veripy.policy (policy.map (·.getString) |>.getD (toString base.policy))
    configs := configs.insert goal (← liftCoreM <| Config.ofOptions options)
  return configs

private def publishReport (name : Name) (report : Report) : CoreM Unit := do
  addCheckedDeclaration (.defnDecl {
    name, levelParams := [], type := mkConst ``Report, value := toExpr report,
    hints := .abbrev, safety := .safe })
  -- Reports are ordinary data, usable by #eval as well as #veripy_report.
  withOptions (fun opts => opts.setBool `Elab.async false) <| compileDecls #[name] (logErrors := false)
  addCheckedDeclaration (.defnDecl {
    name := name.appendAfter "_json", levelParams := [], type := mkConst ``String,
    value := toExpr report.json, hints := .abbrev, safety := .safe })

private def printReport (report : Report) : CommandElabM Unit := do
  for result in report.obligations do
    let location := match result.source with
      | none => s!"byte {result.offset}"
      | some source => s!"{source.path}:{source.line}:{source.column} ({source.label}; byte {result.offset})"
    if result.status == "proved" then
      let provider := if result.provider == "manual" then
        s!"manually: {result.theoremName.getD "unknown"}" else
        s!"via Crush; backend={result.actualBackend.getD "unknown"}, path={result.path.getD "unknown"}"
      logInfo m!"{result.goal}  Proved {provider} [{result.assurance.getD "unknown"}] at {location}"
    else
      logInfo m!"{result.goal}  Pending at {location} ({result.kind}): \
        {result.failureKind.getD "unknown"}\n{result.detail}\n{result.handoff report.imports}"
  if veripy.json.get (← getOptions) then logInfo m!"VERIPY_REPORT {report.json}"

/-- Shared implementation for discovery and strict verification. Keep the
manifest/result declaration names explicit so clients can retrieve the report. -/
def runManifest (manifest : Manifest) (runName : Name) (strict : Bool)
    (base : Config) (configs : NameMap Config := {}) : CommandElabM Report := do
  let environment ← getEnv
  try
    if environment.contains runName || environment.contains (runName ++ `report) then
      throwError "verification result already exists: {runName}"
    -- Assembly rules themselves must remain checked and independent of solver trust.
    discard <| liftCoreM <| audit manifest.assembly .checked
    let identity ← liftCoreM <| fingerprint manifest
    let mut reports := #[]
    let mut proofs := #[]
    for obligation in manifest.obligations do
      let config := configs.find? obligation.goal |>.getD base
      let (proof, report) ← liftTermElabM <| dischargeOne runName obligation config
      if let some proof := proof then proofs := proofs.push proof
      reports := reports.push report
    let complete := proofs.size == manifest.obligations.size
    let mut finalDeclaration := none
    let mut overall := if complete then
      some (if reports.any (·.assurance == some "solver_trusted") then "solver_trusted" else "checked")
      else none
    if strict && complete then
      let value := mkApp (mkConst manifest.assembly) (mkAppN (mkConst manifest.constructor) proofs)
      liftCoreM <| addCheckedDeclaration (.defnDecl {
        name := runName, levelParams := [], type := manifest.resultType, value,
        hints := .abbrev, safety := .safe })
      let policy := if overall == some "solver_trusted" then Policy.solver_trusted else .checked
      let axioms ← liftCoreM <| audit runName policy
      -- A package contains executable admission data as well as proofs. Compile
      -- it before publishing success so downstream definitions and #eval can use
      -- it normally; compilation failures must throw into the rollback path.
      liftCoreM do
        enableRealizationsForConst runName
        if isNoncomputable (← getEnv) manifest.assembly then
          modifyEnv (addNoncomputable · runName)
        else
          withOptions (fun opts => opts.setBool `Elab.async false) <|
            compileDecls #[runName] (logErrors := false)
      overall := some (toString (assurance axioms))
      finalDeclaration := some runName.toString
    let report : Report := {
      manifest := manifest.name.toString, fingerprint := identity,
      imports := #[manifest.origin.toString, "VeriPyAsm.Verification.VC.Registry"],
      resultType := ← liftTermElabM <| fullStatement manifest.resultType,
      complete, finalDeclaration, assurance := overall, obligations := reports }
    printReport report
    if strict && !complete then
      throwError "verification incomplete: {reports.size - proofs.size} unresolved VC(s); no VerifiedArtifact exported"
    liftCoreM <| publishReport (runName ++ `report) report
    return report
  catch error =>
    setEnv environment
    throw error

private def elabRun (strict : Bool) (id manifestId : TSyntax `ident)
    (overrideStxs : Array (TSyntax ``vcOverride)) : CommandElabM Unit := do
  let name := (← getCurrNamespace) ++ id.getId
  let manifestName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo manifestId
  let manifest ← liftCoreM <| getManifest manifestName
  let base ← liftCoreM <| Config.ofOptions (← getOptions)
  let configs ← overrides manifest overrideStxs base
  discard <| runManifest manifest name strict base configs

@[command_elab discoverCommand] def elabDiscover : CommandElab := fun stx => do
  let `(veripy_discover $id:ident from $manifest:ident $[with $overrides:vcOverride*]?) := stx
    | throwUnsupportedSyntax
  elabRun false id manifest (overrides.getD #[])

@[command_elab verifyCommand] def elabVerify : CommandElab := fun stx => do
  let `(veripy_verify $id:ident from $manifest:ident $[with $overrides:vcOverride*]?) := stx
    | throwUnsupportedSyntax
  elabRun true id manifest (overrides.getD #[])

open Elab Term in
elab "#veripy_report " name:ident : command => do
  let reportName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  -- Evaluate only report data, never proof evidence or the truth of a VC.
  let info ← getConstInfo (reportName.appendAfter "_json")
  let some value := info.value? | throwError "expected an emitted VC report"
  let some json := getStringValue? value | throwError "expected report JSON data"
  logInfo json

end VeriPyAsm.Verification.VC
