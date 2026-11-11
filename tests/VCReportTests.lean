import GeneratedScopedCheckpointTests
import VeriPyAsm.Verification.VC.Source
import VeriPyAsm.Examples.Checkpoints.Correctness

namespace VeriPyAsm.Tests.VCReport
open Lean Meta Verification.VC
open GeneratedScopedCheckpoint

def location : SourceLocation where
  path := "example.py"
  digest := "diagnostic-source-digest"
  functionName := "nonnegative"
  label := "hint"
  line := 7
  column := 2
  endLine := 7
  endColumn := 19

def unknown : List (String × SourceLocation) := [("entry", location), ("missing", location)]
/-- error: source binding names unknown VC field missing -/
#guard_msgs in
veripy_vc_sources generated from unknown

def duplicate : List (String × SourceLocation) := [("entry", location), ("entry", location)]
/-- error: duplicate source binding for VC field entry -/
#guard_msgs in
veripy_vc_sources generated from duplicate

def invalid : List (String × SourceLocation) := [("entry", { location with endColumn := 0 })]
/-- error: invalid VC source identity or span -/
#guard_msgs in
veripy_vc_sources generated from invalid

run_cmd Lean.Elab.Command.liftCoreM do
  let manifest ← getManifest ``generated
  unless manifest.obligations.all (·.source.isNone) do
    throwError "failed source attachment leaked metadata"

def sources : List (String × SourceLocation) := [("checkpoint_hint", location)]
veripy_vc_sources generated from sources

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify result from generated

example : result.report.schemaVersion = 2 := rfl
example : result.report.obligations[0]!.source = none := rfl
example : result.report.obligations[3]!.source = some location := rfl
example : result.report.obligations[3]!.provider = "manual" := rfl
example : result.report.obligations[3]!.dependencyScope = "checkpoint_assumptions_upper_bound" := rfl
example : Examples.Checkpoints.verified.report.obligations[2]!.dependencyScope = "unspecified" := rfl
example : result.report.obligations[0]!.dependencies = #[] := rfl
example : result.report.obligations[3]!.dependencies =
    #["VeriPyAsm.Tests.GeneratedScopedCheckpoint.generated.VC.checkpoint_assertion"] := rfl
example : result.report.obligations[3]!.context.binders.any (·.assumption) = true := by decide +kernel

-- Structured contexts reconstruct the exact theorem by rfl, just like the
-- existing unelided manual handoff. Source metadata does not alter any goal.
def awkwardContext : Prop := ∀ («odd name» : Nat), «odd name» > 0 → ∃ n, n + 1 = «odd name»
def dependentContext : Prop := ∀ (α : Type) (x y : α) (h : x = y), h = h

run_cmd Lean.Elab.Command.liftTermElabM do
  let manifest ← getManifest ``generated
  let goals := manifest.obligations.map (fun o => (o.field, o.goal)) ++
    #[(`quoted, ``awkwardContext), (`dependent, ``dependentContext)]
  for (field, goal) in goals do
    let context ← goalContext goal
    let binders := context.binders.toList.map fun binder => s!"∀ ({binder.name} : {binder.type}), "
    let statement := String.join binders ++ context.conclusion
    let .ok parsed := Parser.runParserCategory (← getEnv) `term statement
      | throwError "structured context does not parse: {statement}"
    let type ← Elab.Term.elabType parsed
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    addCheckedDeclaration (.thmDecl {
      name := `VeriPyAsm.Tests.VCReport.contextMatches ++ field, levelParams := [],
      type := ← mkEq type (mkConst goal), value := ← mkEqRefl type })
  unless (← getManifest ``generated).assembly == ``generated.assemble do
    throwError "source attachment changed assembly"
  let original ← fingerprint manifest
  let erased := { manifest with obligations := manifest.obligations.map (fun o => { o with source := none }) }
  if (← fingerprint erased) == original then throwError "source metadata omitted from fingerprint"

#eval show Except String Unit from do
  let decoded ← fromJson? (α := Report) (toJson result.report)
  unless decoded.schemaVersion == 2 && decoded.obligations.size == 4 do
    throw "VC report JSON roundtrip lost metadata"

#veripy_audit VeriPyAsm.Tests.VCReport
end VeriPyAsm.Tests.VCReport
