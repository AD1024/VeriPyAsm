import VeriPyAsm.Verification.VC.GenerateCheckpoints

/-! Proof-producing VC generation for admitted scalar bytecode. The graph walk
is a diagnostic/size analysis, not a trusted soundness oracle. Every generated
VC has a kernel-checked equality to its semantic weakest precondition, and the
assembly applies `Specification.verified` to those exact premises.
-/

namespace VeriPyAsm.Verification.VC

open Lean Meta Elab Command Semantics CPython.V314

open Generation

syntax (name := generateCommand) "veripy_generate " ident " from " ident " for " ident
  (" unfolding " "[" ident,* "]")? : command

@[command_elab generateCommand] def elabGenerate : CommandElab := fun stx => do
  let `(veripy_generate $id:ident from $admissionId:ident for $specId:ident
      $[unfolding [$unfoldIds:ident,*]]?) := stx | throwUnsupportedSyntax
  let environment ← getEnv
  try
    let name := (← getCurrNamespace) ++ id.getId
    if environment.contains name then throwErrorAt id "declaration already exists: {name}"
    let admissionName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo admissionId
    let specName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo specId
    let mut rules := #[specName]
    for unfoldId in unfoldIds.map (·.getElems) |>.getD #[] do
      rules := rules.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo unfoldId)
    let (resultType, obligations, fuel, spec, admission, isScoped, hasCheckpoints, bodyCount) ← liftTermElabM do
      let admission := mkConst admissionName
      let spec := mkConst specName
      for input in #[admissionName, specName] do
        unless (← getConstInfo input).levelParams.isEmpty do
          throwError "VC generation inputs must be closed without universe parameters"
        discard <| audit input .checked
      let admissionType ← whnf (← inferType admission)
      let_expr Admitted artifact := admissionType
        | throwErrorAt admissionId "VC generation requires an Admitted artifact (stack and ownership certificates)"
      let specType ← whnf (← inferType spec)
      let isScoped := specType.isAppOfArity ``ScopedSpecification 1
      let hasCheckpoints := specType.isAppOfArity ``CheckpointSpecification 1
      unless isScoped || hasCheckpoints || specType.isAppOfArity ``Specification 1 do
        throwErrorAt specId "VC generation requires a VC.Specification, VC.ScopedSpecification, or VC.CheckpointSpecification"
      let baseSpec ← if hasCheckpoints then mkAppM ``CheckpointSpecification.base #[spec] else pure spec
      let structural ← mkAppM ``Admitted.toStackAdmitted #[admission]
      let translation ← mkAppM ``StackAdmitted.translation #[structural]
      let code ← mkAppM ``Embedding.Translation.code #[translation]
      let graph ← readGraph code
      let cuts ← (← readList (← mkAppM (if isScoped then ``ScopedSpecification.headers else ``Specification.cutpoints) #[baseSpec])).mapM (fun e => readNat e)
      let fuel ← checkGraph graph cuts
      let mode ← closedWhnf (← mkAppM (if isScoped then ``ScopedSpecification.mode else ``Specification.mode) #[baseSpec])
      let total := mode.isConstOf ``CorrectnessMode.totalCorrectness
      unless total || mode.isConstOf ``CorrectnessMode.partialCorrectness do
        throwError "VC generation requires a concrete correctness mode"
      if total && !cuts.isEmpty then
        if isScoped then
          let loops ← readList (← mkAppM ``ScopedSpecification.loops #[spec])
          for loop in loops do
            let ranking ← closedWhnf (← mkAppM ``ScopedLoop.ranking #[loop])
            unless ranking.isAppOfArity ``Option.some 2 do
              throwError "total correctness requires a ranking function for every scoped loop"
        else
          let ranking ← closedWhnf (← mkAppM ``Specification.ranking #[baseSpec])
          unless ranking.isAppOfArity ``Option.some 2 do
            throwError "total correctness with cutpoints requires a ranking function; set Specification.ranking"
      let program ← mkAppM ``Embedding.compile #[code]
      let programName := name ++ `program
      publishDef programName (mkConst ``Program) program
      let program := mkConst programName
      let representation ← mkEqTrans (← mkAppM ``Embedding.compile_correct #[code])
        (← mkEqSymm (← mkAppM ``Embedding.Translation.correct #[translation]))
      addCheckedDeclaration (.thmDecl {
        name := name ++ `representation, levelParams := [],
        type := ← inferType representation, value := representation })
      let mut lookups := #[]
      for (pc, _) in graph do
        let lookup := mkApp program (mkNatLit pc)
        let instructions ← mkAppM ``Code.instructions #[code]
        let fetched ← closedWhnf (← mkAppM ``fetch #[instructions, mkNatLit pc])
        unless fetched.isAppOfArity ``Option.some 2 do
          throwError "missing decoded instruction at byte {pc}"
        let instruction ← withTransparency .all <| reduce fetched.getAppArgs[1]!
        let command ← mkAppM ``Instruction.denote #[instruction]
        let value ← mkAppM ``Option.some #[command]
        let lookupName := name ++ Name.mkSimple s!"lookup_{pc}"
        addCheckedDeclaration (.thmDecl {
          name := lookupName, levelParams := [], type := ← mkEq lookup value,
          value := ← mkEqRefl lookup })
        lookups := lookups.push lookupName
      let next := mkApp (mkConst ``step) program
      let selected ← if hasCheckpoints then do
          let checks ← mkAppM ``CheckpointSpecification.checkpoints #[spec]
          let length ← mkAppM ``List.length #[checks]
          pure (mkApp (mkConst ``Option.none [.zero]) (mkApp (mkConst ``Fin) length))
        else pure (mkConst ``Unit.unit)
      let mut goals := #[
        (← mkAppM (if isScoped then ``ScopedSpecification.EntryVC else ``Specification.EntryVC) #[artifact, baseSpec]),
        (← if hasCheckpoints then mkAppM ``CheckpointSpecification.InitVC #[next, spec, mkNatLit fuel, selected]
          else mkAppM (if isScoped then ``ScopedSpecification.ExecutionVC else ``Specification.InitVC) #[next, spec, mkNatLit fuel])]
      let mut obligations : Array Obligation := #[
        { field := `entry, goal := name ++ `VC.entry, offset := 0, kind := "entry_compatibility" },
        { field := if isScoped then `execution else `init,
          goal := name ++ `VC ++ (if isScoped then `execution else `init), offset := 0,
          kind := if isScoped then "scoped_execution" else "initialization" }]
      for pc in (if isScoped then #[] else cuts) do
        let field := Name.mkSimple s!"cut{pc}"
        goals := goals.push (← if hasCheckpoints then
          mkAppM ``CheckpointSpecification.BodyVC #[next, spec, mkNatLit fuel, mkNatLit pc, selected]
          else mkAppM ``Specification.BodyVC #[next, spec, mkNatLit fuel, mkNatLit pc])
        obligations := obligations.push {
          field, goal := name ++ `VC ++ field, offset := pc,
          kind := if total then "preservation_and_ranking" else "preservation" }
      if hasCheckpoints then
        let (extraGoals, extraObligations) ← checkpointGoals name next spec fuel graph
        goals := goals ++ extraGoals
        obligations := obligations ++ extraObligations
      for goal in goals, obligation in obligations do
        publishGoal obligation.goal goal rules lookups
      let contract ← mkAppM (if isScoped then ``ScopedSpecification.contract else ``Specification.contract) #[baseSpec]
      let resultType ← mkAppM ``VerifiedArtifact #[artifact, contract, mode]
      return (resultType, obligations, fuel, spec, admission, isScoped, hasCheckpoints, if isScoped then 0 else cuts.size)
    let bundleName := name ++ `Proofs
    if (← getEnv).contains bundleName then
      throwError "declaration already exists: {bundleName}"
    let fieldIds := obligations.map (mkIdent ·.field)
    let goalIds := obligations.map (fun obligation => (mkIdent obligation.goal : TSyntax `term))
    -- Only generated declarations are published synchronously. Input modules
    -- and unrelated Lean elaboration keep their normal checking behavior.
    let errorCount := fun (messages : MessageLog) =>
      messages.reportedPlusUnreported.toArray.filter (fun message => message.severity matches .error) |>.size
    let errorsBefore := errorCount (← get).messages
    withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) do
      elabCommand (← `(command| structure $(mkIdent (rootNamespace ++ bundleName)):ident : Prop where
        $[$fieldIds:ident : $goalIds:term]*))
    -- Command elaboration can log an error and recover instead of throwing.
    -- Such recovery must not be followed by a success diagnostic or manifest.
    if errorCount (← get).messages > errorsBefore then
      throwError "generated proof structure failed to elaborate; no VC manifest exported"
    let assemblyName := name ++ `assemble
    liftTermElabM do
      withLocalDeclD `proofs (mkConst bundleName) fun proofs => do
        let mut rawProofs := #[]
        for obligation in obligations do
          let proof := mkApp (mkConst (bundleName ++ obligation.field)) proofs
          rawProofs := rawProofs.push (← mkAppM ``Eq.mpr
            #[mkConst (obligation.goal ++ `normalization), proof])
        let mut bodies := mkConst ``True.intro
        for proof in (rawProofs.extract 2 (2 + bodyCount)).toList.reverse do
          bodies ← mkAppM ``And.intro #[proof, bodies]
        let arguments := #[admission, spec, mkNatLit fuel, mkConst (name ++ `program),
            mkConst (name ++ `representation), rawProofs[0]!, rawProofs[1]!]
        let assembled ← if hasCheckpoints then do
            let mut checks := mkConst ``True.intro
            for proof in (rawProofs.extract (2 + bodyCount) rawProofs.size).toList.reverse do
              checks ← mkAppM ``And.intro #[proof, checks]
            mkAppM ``CheckpointSpecification.verified (arguments ++ #[bodies, checks])
          else do
            mkAppM (if isScoped then ``ScopedSpecification.verified else ``Specification.verified)
              (if isScoped then arguments else arguments.push bodies)
        publishDef assemblyName (← mkArrow (mkConst bundleName) resultType)
          (← mkLambdaFVars #[proofs] assembled)
        discard <| audit assemblyName .checked
    let manifest : Manifest := {
      name, origin := ← getMainModule, resultType, assembly := assemblyName,
      constructor := (getStructureCtor (← getEnv) bundleName).name, obligations }
    liftCoreM <| publishDef name (mkConst ``Unit) (mkConst ``manifestMarker)
    modifyEnv fun env => manifests.addEntry env manifest
    logInfo m!"generated {obligations.size} VCs for {name} ({fuel} decoded instructions, bound per segment)"
  catch error =>
    setEnv environment
    throw error

end VeriPyAsm.Verification.VC
