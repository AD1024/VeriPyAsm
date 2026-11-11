import GeneratedScopedCheckpointTests
import VCReportTests.PrivateFixture
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
    let statement := (← goalContext goal).statement
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

-- Private helpers cannot be named from this importing module, and the printer's
-- internal names for them do not parse. Both report formats must still read
-- back, at the root of a module with nothing opened, as exactly the named VC.
private def readsBack (certificate : Name) (text : String) (goal : Name) : Elab.Command.CommandElabM Unit :=
  Elab.Command.withScope (fun scope => { scope with currNamespace := .anonymous, openDecls := [] }) <|
    Elab.Command.liftTermElabM do
      if (text.splitOn "_private").length != 1 then throwError "{goal} report names a private declaration"
      let .ok parsed := Parser.runParserCategory (← getEnv) `term text
        | throwError "{goal} report does not parse: {text}"
      let type ← Elab.Term.elabType parsed
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      addCheckedDeclaration (.thmDecl {
        name := certificate, levelParams := [],
        type := ← mkEq type (mkConst goal), value := ← mkEqRefl type })

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover privateHere from PrivateFixture.obligations

-- The fixture's own report was emitted where the helpers are local declarations.
run_cmd do
  for (origin, report) in [(`emittedLocally, PrivateFixture.pending.report), (`emittedHere, privateHere.report)] do
    unless report.obligations.map (·.statementForm) == #["expanded", "expanded", "private_unfolded", "named"] do
      throwError "unexpected statement forms from {origin}"
    for obligation in report.obligations do
      let goal := obligation.goal.toName
      let certificate := `VeriPyAsm.Tests.VCReport.privateReadsBack ++ origin ++ goal
      readsBack (certificate ++ `statement) obligation.statement goal
      readsBack (certificate ++ `context) obligation.context.statement goal
  let shapes := [(``PrivateFixture.nested, "private_unfolded"), (``PrivateFixture.recursive, "private_unfolded"),
    (``PrivateFixture.erasedProof, "private_unfolded"), (``PrivateFixture.applied, "private_unfolded"),
    (``PrivateFixture.withOpaque, "named"), (``PrivateFixture.wellFounded, "named"),
    (``PrivateFixture.withStructure, "named")]
  for (goal, form) in shapes do
    let rendering ← Elab.Command.liftTermElabM <| renderGoal goal
    unless rendering.form == form do throwError "{goal} rendered as {rendering.form}, expected {form}"
    let certificate := `VeriPyAsm.Tests.VCReport.privateReadsBack ++ goal
    readsBack (certificate ++ `statement) rendering.statement goal
    readsBack (certificate ++ `context) rendering.context.statement goal

example : privateHere.report.obligations[3]!.statement =
    "VeriPyAsm.Tests.VCReport.PrivateFixture.finish" := rfl
example : privateHere.report.obligations[3]!.context =
    { conclusion := "VeriPyAsm.Tests.VCReport.PrivateFixture.finish" } := rfl
example : privateHere.report.obligations[2]!.context.binders.size = 2 := rfl
example : privateHere.report.obligations[2]!.context.binders[1]!.assumption = true := rfl

-- The emitted theorem skeletons are executable as written: complete each with a
-- proof, register it through its own attribute, and assemble under checked policy.
run_cmd Elab.Command.withScope (fun scope => { scope with currNamespace := .anonymous, openDecls := [] }) do
  let proofs := [(2, "  intro n nonnegative\n  omega\n"),
    (3, "  intro _\n  exact VeriPyAsm.Examples.Checkpoints.finish\n")]
  for (index, proof) in proofs do
    let skeleton := privateHere.report.obligations[index]!.handoff #[]
    let .ok command := Parser.runParserCategory (← getEnv) `command (skeleton ++ proof)
      | throwError "handoff skeleton does not parse: {skeleton}"
    Elab.Command.elabCommand command
  if (← get).messages.hasErrors then throwError "handoff skeleton does not elaborate"

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify privateVerified from PrivateFixture.obligations

example : privateVerified.report.assurance = some "checked" := rfl
example : privateVerified.report.obligations[2]!.theoremName =
    some "VeriPyAsm.Tests.VCReport.PrivateFixture.hint_manual" := rfl
example : privateVerified.report.obligations[3]!.theoremName =
    some "VeriPyAsm.Tests.VCReport.PrivateFixture.finish_manual" := rfl

#eval show Except String Unit from do
  let decoded ← fromJson? (α := Report) (toJson result.report)
  unless decoded.schemaVersion == 2 && decoded.obligations.size == 4 do
    throw "VC report JSON roundtrip lost metadata"

#veripy_audit VeriPyAsm.Tests.VCReport
end VeriPyAsm.Tests.VCReport
