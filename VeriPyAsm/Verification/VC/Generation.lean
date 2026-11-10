import VeriPyAsm.Verification.VC.ScopedCheckpoint
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
  ``ScopedCheckpointSpecification.ExecutionVC, ``ScopedCheckpointSpecification.SelectedVC,
  ``CheckpointSpecification.InitVC, ``CheckpointSpecification.BodyVC,
  ``CheckpointSpecification.BodiesVC, ``CheckpointSpecification.SelectedVC,
  ``ScopedSpecification.EntryVC, ``ScopedSpecification.ExecutionVC,
  ``ScopedSpecification.post, ``ScopedSpecification.headers, ``ScopedLoop.atHeader,
  ``ScopedLoop.rank, ``ScopedLoop.bodyPost, ``Checkpoint.bodyPost,
  ``Specification.EntryVC, ``Specification.InitVC, ``Specification.BodyVC,
  ``Specification.entryPost, ``Specification.bodyPost, ``Specification.post,
  ``Specification.atCut, ``Specification.rank, ``EntryFrame,
  ``and_imp, ``or_imp, ``exists_imp, ``and_assoc]

def executionRules : Array Name := #[
  ``Checkpoint.regionWP, ``Checkpoint.iterationRegionWP, ``Checkpoint.loopSummary,
  ``Checkpoint.wp, ``Checkpoint.iterationWP, ``Checkpoint.edgeChecks,
  ``Checkpoint.guard, ``Checkpoint.terminal, ``Checkpoint.assertionPass, ``List.finRange_succ,
  ``regionWP, ``iterationRegionWP, ``loopSummary, ``findLoop,
  ``wp, ``iterationWP, ``Postcondition.Accepts, ``step, ``Instruction.denote,
  ``Semantics.Command.jump, ``Semantics.Command.push, ``Semantics.Command.load,
  ``Semantics.Command.store, ``Semantics.Command.binary, ``Semantics.Command.toBool,
  ``branch_split, ``Semantics.Command.ret, ``Semantics.Command.raiseAssertionError,
  ``Semantics.Command.loadPair, ``Semantics.Command.storeLoad, ``Semantics.Command.storePair,
  ``Semantics.binary, ``Semantics.compare, ``Value.asInt, ``Value.truthy, ``Value.pythonEq]

/-- The frame is the last argument, except for edge checks (argument seven).
Partial applications stay opaque until an actual frame supplies a known PC. -/
private def executionArity? (expression : Expr) : Option Nat :=
  match expression.getAppFn with
  | .const name _ => match name with
    | ``wp => some 5
    | ``regionWP | ``iterationRegionWP => some 7
    | ``loopSummary => some 11
    | ``Checkpoint.wp | ``Checkpoint.iterationWP | ``Checkpoint.edgeChecks => some 10
    | ``Checkpoint.regionWP | ``Checkpoint.iterationRegionWP => some 12
    | ``Checkpoint.loopSummary => some 13
    | ``Checkpoint.assertionPass => some 4
    | ``step => some 2
    | _ => none
  | _ => none

def simplify (expression : Expr) (rules : Array Name) : MetaM Simp.Result := do
  let mut theorems ← getSimpTheorems
  let mut checkpointNames : Array Name := #[]
  for rule in rules do
    if (← whnf (← getConstInfo rule).type).isAppOf ``EdgeCheckpoint then
      checkpointNames := checkpointNames.push rule
    theorems ← if (← getConstInfo rule).isTheorem then theorems.addConst rule
      else theorems.addDeclToUnfold rule
  -- Retain lookup/equation proofs instead of asking kernel conversion to
  -- re-execute the decoded dispatcher inside nested continuations.
  let context ← Simp.mkContext (config := { maxSteps := 1000000, contextual := true, implicitDefEqProofs := false })
    (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
  let methods ← Simp.mkDefaultMethods
  let dpre : Simp.DSimproc := fun expression => do
    -- Dependent arguments (notably Fin-indexed checkpoint lists) use dsimp,
    -- which does not call the ordinary simp pre-hook. Preserve the same
    -- execution boundary there, too: only the frame-aware pre-hook may run WP.
    if expression.isAppOf ``EdgeCheckpoint.mk ||
        expression.getAppFn.constName?.any checkpointNames.contains ||
        expression.isAppOf ``ScopedLoop.bodyPost || expression.isAppOf ``Checkpoint.bodyPost ||
        (executionArity? expression).isSome then
      return .done expression
    methods.dpre expression
  let pre : Simp.Simproc := fun expression => do
    -- Checkpoint predicates are data until an actual edge applies them to a
    -- concrete frame. Simplifying their generic function bodies can expand
    -- assertion WPs and change dependent Fin-indexed lists at every step.
    if expression.isAppOf ``EdgeCheckpoint.mk ||
        expression.getAppFn.constName?.any checkpointNames.contains then
      return .done { expr := expression }
    if expression.isAppOfArity ``Checkpoint.assertionPass 4 then
      -- Reduce the exit list before unfolding the WP. Otherwise simp can
      -- explore both sides of an unresolved cut test and expand later loops.
      let args := expression.getAppArgs
      if !args[1]!.hasFVar && !args[1]!.hasMVar then
        let exits ← withTransparency .all <| reduce args[1]!
        if exits != args[1]! then
          return .visit { expr := mkAppN expression.getAppFn (args.set! 1 exits) }
    if expression.isAppOfArity ``Checkpoint.edgeChecks 10 then
      -- Select concrete edges before traversing checkpoint predicates. Each
      -- structural reduction has an explicit equality: omitting skip proofs
      -- can make kernel conversion unfold the following WP instead. Predicate
      -- simplification supplies a congruence proof for an active checkpoint.
      let args := expression.getAppArgs
      let beforePC ← getNatValue? (← whnf (← mkAppM ``Frame.pc #[args[6]!]))
      let currentPC ← getNatValue? (← whnf (← mkAppM ``Frame.pc #[args[7]!]))
      if let (some beforePC, some currentPC) := (beforePC, currentPC) then
        let indices ← withTransparency .all <| whnf args[9]!
        if indices.isAppOfArity ``List.nil 1 then
          return .visit {
            expr := args[8]!
            proof? := some (← mkAppM ``Checkpoint.edgeChecks_nil (args.extract 1 9)) }
        if indices.isAppOfArity ``List.cons 3 then
          let index := indices.getAppArgs[1]!
          let tail := mkAppN expression.getAppFn (args.set! 9 indices.getAppArgs[2]!)
          let checkpoint ← mkAppM ``List.get #[args[2]!, index]
          let edges ← mkAppM ``EdgeCheckpoint.edges #[checkpoint]
          let edge ← mkAppM ``Prod.mk #[mkNatLit beforePC, mkNatLit currentPC]
          let applies ← withTransparency .all <| whnf (← mkAppM ``List.contains #[edges, edge])
          if applies.isConstOf ``Bool.false then
            return .visit {
              expr := tail
              proof? := some (← mkAppM ``Checkpoint.edgeChecks_skip
                ((args.extract 1 9) ++ #[index, indices.getAppArgs[2]!, ← mkEqRefl applies])) }
          if applies.isConstOf ``Bool.true then
            let value ← withTransparency .all <| whnf checkpoint
            let_expr EdgeCheckpoint.mk _ _ _ _ predicate := value
              | throwError "checkpoint did not reduce to a constructor"
            let claim := (mkAppN predicate #[args[1]!, args[3]!, args[4]!, args[7]!]).headBeta
            let reduced ← Simp.simp claim
            let selected ← withTransparency .all <| whnf args[5]!
            let replaceClaim (own : Bool) : SimpM Simp.Step := do
              let function ← withLocalDeclD `claim (mkSort .zero) fun value => do
                let continuation ← mkArrow value tail
                mkLambdaFVars #[value] (if own then mkAnd value continuation else continuation)
              return .visit {
                expr := (mkApp function reduced.expr).headBeta
                proof? := some (← mkCongrArg function (← reduced.getProof)) }
            if selected.isAppOfArity ``Option.none 1 then
              return ← replaceClaim false
            if selected.isAppOfArity ``Option.some 2 then
              let selectedValue ← withTransparency .all <| whnf (← mkAppM ``Fin.val #[selected.getAppArgs[1]!])
              let indexValue ← withTransparency .all <| whnf (← mkAppM ``Fin.val #[index])
              if let (some a, some b) := (← getNatValue? selectedValue, ← getNatValue? indexValue) then
                return ← replaceClaim (a == b)
            return .visit { expr := ← mkAppM ``Checkpoint.guard #[args[5]!, index, claim, tail] }
    -- Keep a loop postcondition opaque until a projection applies it to an
    -- actual outcome. Simplifying its generic continuation expands unused
    -- frame/tag cases and can obscure a false ranking obligation.
    if expression.isAppOf ``ScopedLoop.bodyPost || expression.isAppOf ``Checkpoint.bodyPost then
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
      if post.isAppOf ``ScopedLoop.bodyPost || post.isAppOf ``Checkpoint.bodyPost then
        let pc ← mkAppM ``Frame.pc #[arguments.back!]
        if (← getNatValue? (← whnf pc)).isSome then
          -- Reduce only the record projection. Reducing the whole application
          -- would execute the continuation before using the program lookup lemmas.
          let record ← withTransparency .all <| whnf post
          if record.isAppOfArity ``Postcondition.mk 3 && index < 3 then
            return .visit { expr := mkAppN record.getAppArgs[index]! arguments }
    -- Do not unroll a continuation under an unknown matcher-bound frame.
    -- Once the branch is selected, the concrete PC permits the next segment step.
    if let some arity := executionArity? expression then
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
        let unfolding : Option Simp.Result ← if let some theoremName ← getUnfoldEqnFor? expression.getAppFn.constName! then
            Simp.tryTheorem? expression { origin := .decl theoremName, proof := mkConst theoremName, rfl := false }
          else pure none
        let unfolding : Option Simp.Result ← if unfolding.isSome then pure unfolding else do
          pure ((← unfoldDefinition? expression (ignoreTransparency := true)).map fun expr => ({ expr } : Simp.Result))
        if let some unfolding := unfolding then return .visit unfolding
    -- Reduce the scrutinee before visiting generic matcher branches. In
    -- particular, an if-valued step must select its concrete frames before
    -- simplifying the unused halted continuation of a loop summary.
    let .const matcherName _ := expression.getAppFn | return ← methods.pre expression
    if let some matcher ← getMatcherInfo? matcherName then
      -- Only nondependent, single-scrutinee proposition matches need this
      -- distribution. Other user matches remain ordinary residual Lean terms.
      unless matcher.numDiscrs == 1 && matcher.discrInfos.all (·.hName?.isNone) &&
          (← isProp expression) do return ← methods.pre expression
      let args := expression.getAppArgs
      for index in [matcher.getFirstDiscrPos : matcher.getFirstDiscrPos + matcher.numDiscrs] do
        if index ≥ args.size then continue
        let arg := args[index]!
        let reduced ← Simp.simp arg
        if reduced.expr != arg then
          let function ← withLocalDeclD `scrutinee (← inferType arg) fun value =>
            mkLambdaFVars #[value] (mkAppN expression.getAppFn (args.set! index value))
          return .visit {
            expr := mkAppN expression.getAppFn (args.set! index reduced.expr)
            proof? := some (← mkCongrArg function (← reduced.getProof)) }
        if arg.isAppOfArity ``ite 5 then
          let iteArgs := arg.getAppArgs
          let function ← withLocalDeclD `branch iteArgs[0]! fun branch =>
            mkLambdaFVars #[branch] (mkAppN expression.getAppFn (args.set! index branch))
          let .forallE _ _ resultType _ ← inferType function
            | return ← methods.pre expression
          if resultType.hasLooseBVars then return ← methods.pre expression
          let proof ← mkAppM ``apply_ite #[function, iteArgs[1]!, iteArgs[3]!, iteArgs[4]!]
          let type ← inferType proof
          return .visit { expr := type.getAppArgs[2]!, proof? := some proof }
    methods.pre expression
  return (← Simp.main expression context (methods := { methods with pre, dpre })).1

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
