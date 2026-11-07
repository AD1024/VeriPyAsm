import VeriPyAsm.Verification.VC.Scoped
import VeriPyAsm.Verification.VC.EdgeCheckpoint
import VeriPyAsm.Verification.VC.Manifest

/-! Shared proof-producing normalization and graph diagnostics for VC generators.
All published equalities and assembly functions pass synchronous kernel checking. -/

namespace VeriPyAsm.Verification.VC.Generation
open Lean Meta Elab Command Semantics CPython.V314

initialize registerTraceClass `veripy.generate

def controlFlow (code : Code) : List (Nat × List Nat) :=
  code.instructions.map fun instruction => (instruction.offset, instruction.successors)

def closedWhnf (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasFVar then
    throwError "VC generation requires closed inputs without metavariables"
  match Kernel.whnf (← getEnv) (← getLCtx) expression with
  | .ok result => return result
  | .error error => throwError "VC generation reduction failed: {error.toMessageData (← getOptions)}"

def readNat (expression : Expr) : MetaM Nat := do
  let some value ← getNatValue? (← closedWhnf expression)
    | throwError "VC generation expected a closed natural number"
  return value

def readList (expression : Expr) : MetaM (Array Expr) := do
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

def readGraph (code : Expr) : MetaM (Array (Nat × Array Nat)) := do
  let entries ← readList (← mkAppM ``controlFlow #[code])
  entries.mapM fun entry => do
    let entry ← closedWhnf entry
    let_expr Prod.mk _ _ offset successors := entry
      | throwError "unexpected control-flow graph entry"
    return (← readNat offset, ← (← readList successors).mapM readNat)

/-- Stop at each annotated cut, then check its outgoing paths independently.
A back edge without an intervening cut is rejected even in partial mode: the
finite segment WP must never stand in for a divergent unannotated segment. -/
partial def visit (graph : Array (Nat × Array Nat)) (cuts : Array Nat)
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

def checkGraph (graph : Array (Nat × Array Nat)) (cuts : Array Nat) : MetaM Nat := do
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

def publishDef (name : Name) (type value : Expr) : CoreM Unit := do
  addCheckedDeclaration (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  enableRealizationsForConst name
  withOptions (fun options => options.setBool `Elab.async false) <|
    compileDecls #[name] (logErrors := false)

def shapeRules : Array Name := #[
  ``CheckpointSpecification.InitVC, ``CheckpointSpecification.BodyVC,
  ``CheckpointSpecification.BodiesVC, ``CheckpointSpecification.SelectedVC,
  ``ScopedSpecification.EntryVC, ``ScopedSpecification.ExecutionVC,
  ``ScopedSpecification.post, ``ScopedSpecification.headers, ``ScopedLoop.atHeader,
  ``ScopedLoop.rank, ``ScopedLoop.bodyPost,
  ``Specification.EntryVC, ``Specification.InitVC, ``Specification.BodyVC,
  ``Specification.entryPost, ``Specification.bodyPost, ``Specification.post,
  ``Specification.atCut, ``Specification.rank, ``EntryFrame,
  ``and_imp, ``or_imp, ``exists_imp, ``and_assoc]

def executionRules : Array Name := #[
  ``Checkpoint.wp, ``Checkpoint.iterationWP, ``Checkpoint.edgeChecks,
  ``Checkpoint.guard, ``Checkpoint.terminal, ``Checkpoint.assertionPass, ``List.finRange_succ,
  ``regionWP, ``iterationRegionWP, ``loopSummary, ``findLoop,
  ``wp, ``iterationWP, ``Postcondition.Accepts, ``step, ``Instruction.denote,
  ``Semantics.Command.jump, ``Semantics.Command.push, ``Semantics.Command.load,
  ``Semantics.Command.store, ``Semantics.Command.binary, ``Semantics.Command.toBool,
  ``branch_split, ``Semantics.Command.ret, ``Semantics.Command.raiseAssertionError,
  ``Semantics.Command.loadPair, ``Semantics.Command.storeLoad, ``Semantics.Command.storePair,
  ``Semantics.binary, ``Semantics.compare, ``Value.asInt, ``Value.truthy, ``Value.pythonEq]

def simplify (expression : Expr) (rules : Array Name) : MetaM Simp.Result := do
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
        expression.isAppOf ``iterationRegionWP || expression.isAppOf ``loopSummary ||
        expression.isAppOf ``Checkpoint.wp || expression.isAppOf ``Checkpoint.iterationWP ||
        expression.isAppOf ``Checkpoint.edgeChecks then
      let isCheckpoint := expression.isAppOf ``Checkpoint.wp || expression.isAppOf ``Checkpoint.iterationWP ||
        expression.isAppOf ``Checkpoint.edgeChecks
      let arity := if isCheckpoint then 10 else if expression.isAppOf ``wp then 5
        else if expression.isAppOf ``loopSummary then 11 else 7
      unless expression.getAppNumArgs == arity do return .done { expr := expression }
      let frameIndex := if expression.isAppOf ``Checkpoint.edgeChecks then 7 else arity - 1
      let frame := expression.getAppArgs[frameIndex]!
      let pc ← mkAppM ``Frame.pc #[frame]
      unless (← getNatValue? (← whnf pc)).isSome do
        -- A context equality may supply the concrete frame. Blocking the entire
        -- application here would also block that substitution under preconditions.
        let reduced ← Simp.simp frame
        if reduced.expr != frame then
          let function ← withLocalDeclD `frame (mkConst ``Frame) fun value =>
            mkLambdaFVars #[value] (mkAppN expression.getAppFn (expression.getAppArgs.set! frameIndex value))
          let proof ← mkCongrArg function (← reduced.getProof)
          return .visit { expr := (mkApp function reduced.expr).headBeta, proof? := some proof }
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

def publishGoal (name : Name) (raw : Expr) (rules lookups : Array Name) : MetaM Unit := do
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

end VeriPyAsm.Verification.VC.Generation
