import VeriPyAsm.Verification.VC.Manifest

/-! Complete manual handoffs and machine-readable evidence reports. Fingerprints
are diagnostic identities, never proof cache keys or substitutes for checking.
-/

namespace VeriPyAsm.Verification.VC

open Lean Meta Elab

/-- The outer quantified context of the exact VC. Names are unique within a
context; the conclusion retains any further branch-local quantification. -/
structure ContextBinder where
  name : String
  type : String
  assumption : Bool
  deriving Inhabited, ToJson, FromJson, ToExpr

structure GoalContext where
  binders : Array ContextBinder := #[]
  conclusion : String := ""
  deriving Inhabited, ToJson, FromJson, ToExpr

/-- The single proposition a context denotes: its binders, in order, around its
conclusion. This is the reconstruction consumers of the report should use. -/
def GoalContext.statement (context : GoalContext) : String :=
  String.join (context.binders.toList.map fun binder => s!"∀ ({binder.name} : {binder.type}), ")
    ++ context.conclusion

structure ObligationReport where
  goal : String
  offset : Nat
  kind : String
  statement : String
  source : Option SourceLocation := none
  context : GoalContext := {}
  /-- How `statement` and `context` spell the VC: `expanded` (its definition
  unfolded), `private_unfolded` (private definitions also replaced by their
  values), or `named` (the VC's own name, when no expansion can be written
  in another module). Every form is the complete obligation. -/
  statementForm : String := "expanded"
  dependencies : Array String := #[]
  dependencyScope : String := "unspecified"
  status : String
  provider : String := "none"
  theoremName : Option String := none
  policy : String
  assurance : Option String := none
  axioms : Array String := #[]
  configuredBackend : String
  actualBackend : Option String := none
  path : Option String := none
  timeoutSeconds : Nat
  elapsedMs : Nat := 0
  failureKind : Option String := none
  detail : String := ""
  events : Array String := #[]
  deriving Inhabited, ToJson, FromJson, ToExpr

structure Report where
  schemaVersion : Nat := 2
  manifest : String
  fingerprint : String
  imports : Array String
  resultType : String
  complete : Bool
  finalDeclaration : Option String := none
  assurance : Option String := none
  obligations : Array ObligationReport
  deriving Inhabited, ToJson, FromJson, ToExpr

/-- Disable elision and notation hiding for a complete handoff. No simplifier
changes the statement. Printing alone does not make the text parseable: see
`renderGoal`, which decides what may be published as a VC statement. -/
def fullStatement (expression : Expr) : MetaM String :=
  withOptions (fun options => options
    |>.setBool `pp.all true
    |>.setBool `pp.universes true
    |>.setBool `pp.fullNames true
    |>.setBool `pp.proofs true
    |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (1000000 : Nat)) do
    return (← ppExpr expression).pretty 100

private partial def contextOf (expression : Expr) (binders : Array ContextBinder := #[]) :
    MetaM GoalContext := do
  if let .forallE _ type body info := expression then
    let assumption ← isProp type
    -- Stable identifiers also work for quoted/inaccessible input binder names.
    let unique := Name.mkSimple s!"{if assumption then "h" else "v"}{binders.size}"
    let binder : ContextBinder := {
      name := unique.toString, type := ← fullStatement type, assumption }
    return ← withLocalDecl unique info type fun value =>
      contextOf (body.instantiate1 value) (binders.push binder)
  return { binders, conclusion := ← fullStatement expression }

/-- An identifier spells string components only. Private (`_private.M.0.x`) and
hygienic names carry numeric ones: the printer's output for them does not parse,
and a private declaration cannot be named from another module in any case. -/
private def writable : Name → Bool
  | .anonymous => true
  | .str parent _ => writable parent
  | .num .. => false

private def mentionsUnwritable (expression : Expr) : Bool :=
  (expression.find? fun
    | .const name _ => !writable name
    | _ => false).isSome

/-- Replace references to transparent private definitions by their values.
Irreducible definitions, theorems, types, constructors, and opaque constants
are left alone: they have no value a reader should see, or none at all. -/
private def exposePrivate (expression : Expr) : CoreM Expr :=
  Core.transform expression (pre := fun candidate => do
    let .const name levels := candidate.getAppFn | return .continue
    unless isPrivateName name do return .continue
    let info@(.defnInfo _) ← getConstInfo name | return .continue
    if ← isIrreducible name then return .continue
    return .visit ((← instantiateValueLevelParams info levels).beta candidate.getAppArgs))

/-- The registration criterion applied to emitted text. Read it as the top of a
fresh module would (root namespace, nothing opened), then have the kernel check
`Eq.refl : text = goal`. Nothing is added to the environment, and a failure for
any reason, including resource limits, only selects a more conservative form. -/
private def roundTrips (text : String) (goal : Name) : MetaM Bool := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text | return false
  let check : TermElabM Bool := do
    let type ← Term.withoutErrToSorry <| Term.elabType parsed
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    if type.hasMVar || type.hasFVar || type.hasSorry then return false
    let certificate := Declaration.thmDecl {
      name := goal ++ `veripy_report_roundtrip, levelParams := []
      type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero) type (mkConst goal)
      value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkSort .zero) type }
    let options := (← getOptions).setBool `debug.skipKernelTC false
    return ((← getEnv).addDeclCore (Core.getMaxHeartbeats options).toUSize
      (maxRecDepth.get options).toUSize certificate (← readThe Core.Context).cancelTk?).toBool
  withoutModifyingState <| tryCatchRuntimeEx
    (withTheReader Core.Context
      (fun context => { context with currNamespace := .anonymous, openDecls := [] }) check.run')
    fun error => if error.isInterrupt then throw error else pure false

structure GoalRendering where
  form : String
  statement : String
  context : GoalContext

/-- Choose the most informative spelling of a VC that another module can read.

Only the VC definition is unfolded for the ordinary `expanded` form; Lean
operators and library definitions keep their ordinary meaning. If that mentions
a name no identifier can spell, transparent private definitions are replaced by
their values, and the printed statement and context must each parse, elaborate,
and equal the VC by kernel-checked `rfl`. Otherwise the report states the VC by
its own name, which registering a proof from another module requires anyway. -/
def renderGoal (name : Name) : MetaM GoalRendering := do
  discard <| goalExpr name
  let some value := (← getConstInfo name).value? | throwError "missing VC definition"
  let expanded ← withTransparency .all <| whnf (mkConst name)
  if !mentionsUnwritable expanded && !mentionsUnwritable value then
    return { form := "expanded", statement := ← fullStatement expanded, context := ← contextOf value }
  let exposed ← exposePrivate expanded
  let exposedValue ← exposePrivate value
  unless mentionsUnwritable exposed || mentionsUnwritable exposedValue do
    let candidate : GoalRendering := {
      form := "private_unfolded", statement := ← fullStatement exposed
      context := ← contextOf exposedValue }
    if ← roundTrips candidate.statement name <&&> roundTrips candidate.context.statement name then
      return candidate
  return { form := "named", statement := name.toString, context := { conclusion := name.toString } }

def goalStatement (name : Name) : MetaM String := return (← renderGoal name).statement

def goalContext (name : Name) : MetaM GoalContext := return (← renderGoal name).context

/-- Hash the transitive declaration content of artifact, contract, assembly,
semantics, and VCs, together with the workflow and Lean versions. Imported
dependencies used by those declarations are included. Every proof is still
checked afresh; a hash collision cannot authorize proof reuse. -/
def fingerprint (manifest : Manifest) : CoreM String := do
  let environment ← getEnv
  let mut pending := manifest.resultType.getUsedConstants ++ #[manifest.assembly]
    ++ manifest.obligations.map (·.goal)
  let mut seen : NameSet := {}
  let mut contents : Array (Name × UInt64) := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := environment.checked.get.find? name
      | throwError "fingerprint dependency is not kernel checked: {name}"
    let value := info.value? (allowOpaque := true)
    contents := contents.push (name, hash (info.levelParams, info.type, value))
    pending := pending ++ info.type.getUsedConstants
    if let some value := value then pending := pending ++ value.getUsedConstants
  contents := contents.qsort (fun a b => Name.quickLt a.1 b.1)
  return toString <| hash ("veripy-vc-v2", Lean.versionString, contents,
    manifest.obligations.map (fun o => (o.goal, o.offset, o.kind, o.source, o.dependencies, o.dependencyScope)))

def ObligationReport.handoff (report : ObligationReport) (imports : Array String) : String :=
  let note := match report.statementForm with
    | "private_unfolded" =>
      "  -- Private definitions are unfolded above; the statement still equals the VC by rfl.\n"
    | "named" =>
      "  -- Stated by name: the expanded VC mentions declarations other modules cannot write.\n"
    | _ => ""
  String.intercalate "\n" (imports.toList.map ("import " ++ ·)) ++
  s!"\n\n@[veripy_proof {report.goal}]\ntheorem {report.goal}_manual :\n  {report.statement} := by\n{note}  -- Supply your proof here.\n"

def Report.json (report : Report) : String := (toJson report).compress

end VeriPyAsm.Verification.VC
