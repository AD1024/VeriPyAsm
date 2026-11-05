import VeriPyAsm.Verification.VC.Manifest

/-! Complete manual handoffs and machine-readable evidence reports. Fingerprints
are diagnostic identities, never proof cache keys or substitutes for checking.
-/

namespace VeriPyAsm.Verification.VC

open Lean Meta

structure ObligationReport where
  goal : String
  offset : Nat
  kind : String
  statement : String
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
  schemaVersion : Nat := 1
  manifest : String
  fingerprint : String
  imports : Array String
  resultType : String
  complete : Bool
  finalDeclaration : Option String := none
  assurance : Option String := none
  obligations : Array ObligationReport
  deriving Inhabited, ToJson, FromJson, ToExpr

/-- Disable elision and notation hiding for a complete, parseable handoff.
Only the VC definition is unfolded; Lean operators and library definitions keep
their ordinary meaning. No simplifier changes the statement. -/
def fullStatement (expression : Expr) : MetaM String :=
  withOptions (fun options => options
    |>.setBool `pp.all true
    |>.setBool `pp.universes true
    |>.setBool `pp.fullNames true
    |>.setBool `pp.proofs true
    |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (1000000 : Nat)) do
    return (← ppExpr expression).pretty 100

def goalStatement (name : Name) : MetaM String := do
  discard <| goalExpr name
  let expanded ← withTransparency .all <| whnf (mkConst name)
  fullStatement expanded

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
  return toString <| hash ("veripy-vc-v1", Lean.versionString, contents,
    manifest.obligations.map (fun o => (o.goal, o.offset, o.kind)))

def ObligationReport.handoff (report : ObligationReport) (imports : Array String) : String :=
  String.intercalate "\n" (imports.toList.map ("import " ++ ·)) ++
  s!"\n\n@[veripy_proof {report.goal}]\ntheorem {report.goal}_manual :\n  {report.statement} := by\n  -- Supply your proof here.\n"

def Report.json (report : Report) : String := (toJson report).compress

end VeriPyAsm.Verification.VC
