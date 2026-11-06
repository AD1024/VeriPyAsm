import VeriPyAsm.Verification.VC.Scoped
import VeriPyAsm.Verification.VC.Manifest

/-! Proof-producing VC generation for admitted scalar bytecode. The graph walk
is a diagnostic/size analysis, not a trusted soundness oracle. Every generated
VC has a kernel-checked equality to its semantic weakest precondition, and the
assembly applies `Specification.verified` to those exact premises.
-/

namespace VeriPyAsm.Verification.VC

open Lean Meta Elab Command Semantics CPython.V314

initialize registerTraceClass `veripy.generate

private def controlFlow (code : Code) : List (Nat × List Nat) :=
  code.instructions.map fun instruction => (instruction.offset, instruction.successors)

private def closedWhnf (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasFVar then
    throwError "VC generation requires closed inputs without metavariables"
  match Kernel.whnf (← getEnv) (← getLCtx) expression with
  | .ok result => return result
  | .error error => throwError "VC generation reduction failed: {error.toMessageData (← getOptions)}"

private def readNat (expression : Expr) : MetaM Nat := do
  let some value ← getNatValue? (← closedWhnf expression)
    | throwError "VC generation expected a closed natural number"
  return value

private def readList (expression : Expr) : MetaM (Array Expr) := do
  let mut result := #[]
  let mut rest := expression
  repeat
    let reduced ← closedWhnf rest
    if reduced.isAppOfArity ``List.nil 1 then return result
    unless reduced.isAppOfArity ``List.cons 3 do
      throwError "VC generation expected a closed list"
    result := result.push reduced.getAppArgs[1]!
    rest := reduced.getAppArgs[2]!
  return result

private def readGraph (code : Expr) : MetaM (Array (Nat × Array Nat)) := do
  let entries ← readList (← mkAppM ``controlFlow #[code])
  entries.mapM fun entry => do
    let entry ← closedWhnf entry
    let_expr Prod.mk _ _ offset successors := entry
      | throwError "unexpected control-flow graph entry"
    return (← readNat offset, ← (← readList successors).mapM readNat)

/-- Stop at each annotated cut, then check its outgoing paths independently.
A back edge without an intervening cut is rejected even in partial mode: the
finite segment WP must never stand in for a divergent unannotated segment. -/
private partial def visit (graph : Array (Nat × Array Nat)) (cuts : Array Nat)
    (pc : Nat) (path done : Array Nat) : MetaM (Array Nat) := do
  if cuts.contains pc || done.contains pc then return done
  if path.contains pc then
    throwError "unannotated control-flow cycle at byte {pc}; add a cutpoint invariant (path {path.toList})"
  let some (_, successors) := graph.find? (·.1 == pc)
    | throwError "control-flow target {pc} is not a decoded instruction boundary"
  let mut done := done
  for successor in successors do
    done ← visit graph cuts successor (path.push pc) done
  return done.push pc

private def checkGraph (graph : Array (Nat × Array Nat)) (cuts : Array Nat) : MetaM Nat := do
  let mut seen := #[]
  for pc in cuts do
    if seen.contains pc then throwError "duplicate cutpoint at byte {pc}"
    unless graph.any (·.1 == pc) do
      throwError "cutpoint {pc} is not a decoded instruction boundary"
    seen := seen.push pc
  let mut done ← visit graph cuts 0 #[] #[]
  for pc in cuts do
    let some (_, successors) := graph.find? (·.1 == pc)
      | throwError "missing cutpoint instruction {pc}"
    for successor in successors do
      done ← visit graph cuts successor #[pc] done
  -- A path in the remaining DAG visits at most this many instructions. The
  -- semantic proof checks the bound independently via wp's False exhaustion.
  return graph.size

private def publishDef (name : Name) (type value : Expr) : CoreM Unit := do
  addCheckedDeclaration (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  enableRealizationsForConst name
  withOptions (fun options => options.setBool `Elab.async false) <|
    compileDecls #[name] (logErrors := false)

private def shapeRules : Array Name := #[
  ``ScopedSpecification.EntryVC, ``ScopedSpecification.ExecutionVC,
  ``ScopedSpecification.post, ``ScopedSpecification.headers, ``ScopedLoop.atHeader,
  ``ScopedLoop.rank, ``ScopedLoop.bodyPost,
  ``Specification.EntryVC, ``Specification.InitVC, ``Specification.BodyVC,
  ``Specification.entryPost, ``Specification.bodyPost, ``Specification.post,
  ``Specification.atCut, ``Specification.rank, ``EntryFrame,
  ``and_imp, ``or_imp, ``exists_imp, ``and_assoc]

private def executionRules : Array Name := #[
  ``regionWP, ``iterationRegionWP, ``loopSummary, ``findLoop,
  ``wp, ``iterationWP, ``Postcondition.Accepts, ``step, ``Instruction.denote,
  ``Semantics.Command.jump, ``Semantics.Command.push, ``Semantics.Command.load,
  ``Semantics.Command.store, ``Semantics.Command.binary, ``Semantics.Command.toBool,
  ``branch_split, ``Semantics.Command.ret, ``Semantics.Command.raiseAssertionError,
  ``Semantics.Command.loadPair, ``Semantics.Command.storeLoad, ``Semantics.Command.storePair,
  ``Semantics.binary, ``Semantics.compare, ``Value.asInt, ``Value.truthy, ``Value.pythonEq]

private def simplify (expression : Expr) (rules : Array Name) : MetaM Simp.Result := do
  let mut theorems ← getSimpTheorems
  for rule in rules do
    theorems ← if (← getConstInfo rule).isTheorem then theorems.addConst rule
      else theorems.addDeclToUnfold rule
  let context ← Simp.mkContext (config := { maxSteps := 1000000, contextual := true })
    (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
  let methods ← Simp.mkDefaultMethods
  let pre : Simp.Simproc := fun expression => do
    -- Keep a loop postcondition opaque until a projection applies it to an
    -- actual outcome. Simplifying its generic continuation expands unused
    -- frame/tag cases and can obscure a false ranking obligation.
    if expression.isAppOf ``ScopedLoop.bodyPost then
      return .done { expr := expression }
    let projection? :=
      if expression.isAppOfArity ``Postcondition.continues 2 then
        some (expression.getAppArgs[0]!, 0, #[expression.getAppArgs[1]!])
      else if expression.isAppOfArity ``Postcondition.returned 3 then
        some (expression.getAppArgs[0]!, 1, expression.getAppArgs.extract 1 3)
      else if expression.isAppOfArity ``Postcondition.raises 3 then
        some (expression.getAppArgs[0]!, 2, expression.getAppArgs.extract 1 3)
      else match expression with
        | .app (.proj ``Postcondition 0 post) frame => some (post, 0, #[frame])
        | .app (.app (.proj ``Postcondition index post) value) frame => some (post, index, #[value, frame])
        | _ => none
    if let some (post, index, arguments) := projection? then
      if post.isAppOf ``ScopedLoop.bodyPost then
        let pc ← mkAppM ``Frame.pc #[arguments.back!]
        if (← getNatValue? (← whnf pc)).isSome then
          -- Reduce only the record projection. Reducing the whole application
          -- would execute the continuation before using the program lookup lemmas.
          let record ← withTransparency .all <| whnf post
          if record.isAppOfArity ``Postcondition.mk 3 && index < 3 then
            return .visit { expr := mkAppN record.getAppArgs[index]! arguments }
    -- Do not unroll a continuation under an unknown matcher-bound frame.
    -- Once the branch is selected, the concrete PC permits the next segment step.
    if expression.isAppOf ``wp || expression.isAppOf ``regionWP ||
        expression.isAppOf ``iterationRegionWP || expression.isAppOf ``loopSummary then
      let arity := if expression.isAppOf ``wp then 5
        else if expression.isAppOf ``loopSummary then 11 else 7
      unless expression.getAppNumArgs == arity do return .done { expr := expression }
      let frame := expression.getAppArgs[arity - 1]!
      let pc ← mkAppM ``Frame.pc #[frame]
      unless (← getNatValue? (← whnf pc)).isSome do
        -- A context equality may supply the concrete frame. Blocking the entire
        -- application here would also block that substitution under preconditions.
        let reduced ← Simp.simp frame
        if reduced.expr != frame then
          let function := expression.appFn!
          let proof ← mkCongrArg function (← reduced.getProof)
          return .visit { expr := mkApp function reduced.expr, proof? := some proof }
        return .done { expr := expression }
      if rules.contains expression.getAppFn.constName! then
        if let some unfolded ← unfoldDefinition? expression then
          return .visit { expr := unfolded }
    methods.pre expression
  let post : Simp.Simproc := fun expression => do
    -- Distribute through a matcher only. A global apply_ite simp rule also
    -- distributes through ite itself, repeatedly swapping nested conditions.
    let .const matcherName _ := expression.getAppFn | return ← methods.post expression
    if let some matcher ← getMatcherInfo? matcherName then
      -- Only nondependent, single-scrutinee proposition matches need this
      -- distribution. Other user matches remain ordinary residual Lean terms.
      unless matcher.numDiscrs == 1 && matcher.discrInfos.all (·.hName?.isNone) &&
          (← isProp expression) do return ← methods.post expression
      let args := expression.getAppArgs
      for index in [matcher.getFirstDiscrPos : matcher.getFirstDiscrPos + matcher.numDiscrs] do
        if index ≥ args.size then continue
        let arg := args[index]!
        if arg.isAppOfArity ``ite 5 then
          let iteArgs := arg.getAppArgs
          let function ← withLocalDeclD `branch iteArgs[0]! fun branch =>
            mkLambdaFVars #[branch] (mkAppN expression.getAppFn (args.set! index branch))
          let .forallE _ _ resultType _ ← inferType function
            | return ← methods.post expression
          if resultType.hasLooseBVars then return ← methods.post expression
          let proof ← mkAppM ``apply_ite #[function, iteArgs[1]!, iteArgs[3]!, iteArgs[4]!]
          let type ← inferType proof
          return .visit { expr := type.getAppArgs[2]!, proof? := some proof }
    methods.post expression
  return (← Simp.main expression context (methods := { methods with pre, post })).1

private def publishGoal (name : Name) (raw : Expr) (rules lookups : Array Name) : MetaM Unit := do
  -- Eliminate frame equalities and existential shape annotations before
  -- unfolding symbolic execution; this avoids expanding unknown stack shapes.
  let shaped ← simplify raw (shapeRules ++ rules)
  trace[veripy.generate] "{name} after frame normalization:\n{shaped.expr}"
  let reduced ← simplify shaped.expr (shapeRules ++ executionRules ++ rules ++ lookups)
  let normalized ← instantiateMVars reduced.expr
  if normalized.hasMVar || normalized.hasFVar || normalized.hasSorry then
    throwError "VC normalization left unresolved variables or sorry"
  publishDef name (mkSort .zero) normalized
  let first ← shaped.getProof
  let second ← reduced.getProof
  let equality ← mkEqTrans first second
  addCheckedDeclaration (.thmDecl {
    name := name ++ `normalization, levelParams := [],
    type := ← mkEq raw (mkConst name), value := equality })
  discard <| audit (name ++ `normalization) .checked

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
    let (resultType, obligations, fuel, spec, admission, isScoped) ← liftTermElabM do
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
      unless isScoped || specType.isAppOfArity ``Specification 1 do
        throwErrorAt specId "VC generation requires a VC.Specification or VC.ScopedSpecification"
      let structural ← mkAppM ``Admitted.toStackAdmitted #[admission]
      let translation ← mkAppM ``StackAdmitted.translation #[structural]
      let code ← mkAppM ``Embedding.Translation.code #[translation]
      let graph ← readGraph code
      let cuts ← (← readList (← mkAppM (if isScoped then ``ScopedSpecification.headers else ``Specification.cutpoints) #[spec])).mapM (fun e => readNat e)
      let fuel ← checkGraph graph cuts
      let mode ← closedWhnf (← mkAppM (if isScoped then ``ScopedSpecification.mode else ``Specification.mode) #[spec])
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
          let ranking ← closedWhnf (← mkAppM ``Specification.ranking #[spec])
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
      let mut goals := #[
        (← mkAppM (if isScoped then ``ScopedSpecification.EntryVC else ``Specification.EntryVC) #[artifact, spec]),
        (← mkAppM (if isScoped then ``ScopedSpecification.ExecutionVC else ``Specification.InitVC) #[next, spec, mkNatLit fuel])]
      let mut obligations : Array Obligation := #[
        { field := `entry, goal := name ++ `VC.entry, offset := 0, kind := "entry_compatibility" },
        { field := if isScoped then `execution else `init,
          goal := name ++ `VC ++ (if isScoped then `execution else `init), offset := 0,
          kind := if isScoped then "scoped_execution" else "initialization" }]
      for pc in (if isScoped then #[] else cuts) do
        let field := Name.mkSimple s!"cut{pc}"
        goals := goals.push (← mkAppM ``Specification.BodyVC #[next, spec, mkNatLit fuel, mkNatLit pc])
        obligations := obligations.push {
          field, goal := name ++ `VC ++ field, offset := pc,
          kind := if total then "preservation_and_ranking" else "preservation" }
      for goal in goals, obligation in obligations do
        publishGoal obligation.goal goal rules lookups
      let contract ← mkAppM (if isScoped then ``ScopedSpecification.contract else ``Specification.contract) #[spec]
      let resultType ← mkAppM ``VerifiedArtifact #[artifact, contract, mode]
      return (resultType, obligations, fuel, spec, admission, isScoped)
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
        for proof in rawProofs.toList.drop 2 |>.reverse do
          bodies ← mkAppM ``And.intro #[proof, bodies]
        let arguments := #[admission, spec, mkNatLit fuel, mkConst (name ++ `program),
            mkConst (name ++ `representation), rawProofs[0]!, rawProofs[1]!]
        let assembled ← mkAppM (if isScoped then ``ScopedSpecification.verified else ``Specification.verified)
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
