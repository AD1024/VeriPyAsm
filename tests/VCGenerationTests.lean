import VeriPyAsm.Examples.Triangular.GeneratedProofs

namespace VeriPyAsm.Tests.VCGeneration

open Semantics Verification CPython.V314 Examples
open Lean Meta Elab Command

-- The generated loop verifies the same artifact and contract without importing
-- any of the hand-written summaries or their proof providers.
example : ArtifactTotalCorrect triangularArtifact triangularContract :=
  Triangular.GeneratedProofs.verified.artifact_total

#eval show CoreM Unit from do
  for name in [`VeriPyAsm.Examples.Triangular.entry,
      `VeriPyAsm.Examples.Triangular.Assembly.verified,
      `VeriPyAsm.Examples.Triangular.Arithmetic.proofs] do
    if (← getEnv).contains name then throwError "generation imported the hand-written proof: {name}"

def adder : Admitted add1Artifact := admit_bytecode% add1Artifact

def addition : VC.Specification Int where
  contract := {
    pre := fun n initial => initial = { locals := [some (.int n)] }
    post := fun n initial value final =>
      value = .int (n + 1) ∧ final.locals = initial.locals ∧ final.stack = []
    raises := fun _ _ _ _ => False }

#guard_msgs (drop info, all) in
veripy_generate addGoals from adder for addition

@[veripy_proof addGoals.VC.entry]
theorem add_entry : addGoals.VC.entry := by
  intro n
  exact ⟨[.int n], rfl, rfl⟩

@[veripy_proof addGoals.VC.init]
theorem add_init : addGoals.VC.init := True.intro

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_verify added from addGoals

example : ArtifactTotalCorrect add1Artifact addition.contract := added.artifact_total

-- Transport also supports admitted shallow programs that are propositionally,
-- rather than definitionally, the canonical translation.
def alternateProgram : Program := fun pc =>
  if pc + 0 = 0 + pc then adder.translation.program pc else none

theorem alternateProgram_equal : alternateProgram = adder.translation.program := by
  funext pc
  simp [alternateProgram]

def alternate : Admitted add1Artifact where
  translation := {
    adder.translation with
    program := alternateProgram
    correct := by rw [alternateProgram_equal]; exact adder.translation.correct }
  stack := adder.stack
  ownership := adder.ownership

#guard_msgs (drop info, all) in
veripy_generate alternateGoals from alternate for addition

example : VerifiedArtifact add1Artifact addition.contract :=
  alternateGoals.assemble ⟨by intro n; exact ⟨[.int n], rfl, rfl⟩, True.intro⟩

-- Branches retain both the normal return and the modeled exception snapshot.
def checkedAdmission : Admitted checkedArtifact := admit_bytecode% checkedArtifact

def checkedSpec : VC.Specification Bool where
  contract := {
    pre := fun flag initial => initial = { locals := [some (.bool flag), none] }
    post := fun flag _ value final => flag = true ∧ value = .int 1 ∧ final.stack = []
    raises := fun flag _ exception final =>
      flag = false ∧ exception = .unboundLocalError ∧ final.pc = 22 ∧ final.stack = [] }

#guard_msgs (drop info, all) in
veripy_generate checkedGoals from checkedAdmission for checkedSpec

example : VerifiedArtifact checkedArtifact checkedSpec.contract :=
  checkedGoals.assemble
    ⟨⟨⟨[.bool false], rfl, rfl⟩, ⟨[.bool true], rfl, rfl⟩⟩, True.intro⟩

def forbiddenException : VC.Specification Bool :=
  { checkedSpec with contract := { checkedSpec.contract with raises := fun _ _ _ _ => False } }

#guard_msgs (drop info, all) in
veripy_generate exceptionGoals from checkedAdmission for forbiddenException unfolding [checkedSpec]

example : ¬ exceptionGoals.VC.init := by simp [exceptionGoals.VC.init]

-- Wrong functional claims and faulty unchecked loads remain false VCs.
def wrongAddition : VC.Specification Int :=
  { addition with contract := { addition.contract with
      post := fun n _ value _ => value = .int (n + 2) } }

#guard_msgs (drop info, all) in
veripy_generate wrongGoals from adder for wrongAddition unfolding [addition]

example : ¬ wrongGoals.VC.init := by simp [wrongGoals.VC.init]

def faulty : VC.Specification Unit where
  contract := {
    pre := fun _ initial => initial = { locals := [none] }
    post := fun _ _ _ _ => True
    raises := fun _ _ _ _ => True }

#guard_msgs (drop info, all) in
veripy_generate faultGoals from adder for faulty

example : ¬ faultGoals.VC.init := by simp [faultGoals.VC.init]

-- The bytecode returns normally from this state, but it is outside call entry.
-- The functional VC alone must not be enough to produce a final package.
def invalidEntry : VC.Specification Int where
  contract := {
    pre := fun n initial => initial = { pc := 18, locals := [some (.int n)], stack := [.int n] }
    post := fun n _ value _ => value = .int n
    raises := fun _ _ _ _ => False }

#guard_msgs (drop info, all) in
veripy_generate entryGoals from adder for invalidEntry

example : ¬ entryGoals.VC.entry := by simp [entryGoals.VC.entry]
example : entryGoals.VC.init := True.intro

-- A genuine infinite loop is verifiable in partial mode. Reaching the same
-- cutpoint with zero steps cannot manufacture total correctness.
def foreverArtifact : Artifact :=
  { literalArtifact with name := "forever", code := [128, 0, 75, 2, 0, 0], stackSize := 0 }

def forever : Admitted foreverArtifact := admit_bytecode% foreverArtifact

def partialLoop : VC.Specification Unit where
  contract := {
    pre := fun _ initial => initial = {}
    post := fun _ _ _ _ => False
    raises := fun _ _ _ _ => False }
  mode := .partialCorrectness
  cutpoints := [2]
  invariant _ _ current := current = { pc := 2 }

#guard_msgs (drop info, all) in
veripy_generate partialGoals from forever for partialLoop

example : VerifiedArtifact foreverArtifact partialLoop.contract .partialCorrectness :=
  partialGoals.assemble ⟨by exact ⟨[], rfl, rfl, rfl⟩, True.intro, True.intro⟩

def multipleCuts : VC.Specification Unit :=
  { partialLoop with
    cutpoints := [0, 2]
    invariant := fun _ _ current => current = ({ } : Frame) ∨ current = { pc := 2 } }

#guard_msgs (drop info, all) in
veripy_generate multipleGoals from forever for multipleCuts unfolding [partialLoop]

example : VerifiedArtifact foreverArtifact partialLoop.contract .partialCorrectness :=
  multipleGoals.assemble ⟨by exact ⟨[], rfl, rfl, rfl⟩,
    by simp [multipleGoals.VC.init], by simp [multipleGoals.VC.cut0], by simp [multipleGoals.VC.cut2]⟩

def noCut : VC.Specification Unit := { partialLoop with cutpoints := [] }

/-- error: unannotated control-flow cycle at byte 2; add a cutpoint invariant (path [0, 2]) -/
#guard_msgs in
veripy_generate uncovered from forever for noCut

def duplicateCut : VC.Specification Unit := { partialLoop with cutpoints := [2, 2] }

/-- error: duplicate cutpoint at byte 2 -/
#guard_msgs in
veripy_generate duplicate from forever for duplicateCut

def cacheCut : VC.Specification Unit := { partialLoop with cutpoints := [4] }

/-- error: cutpoint 4 is not a decoded instruction boundary -/
#guard_msgs in
veripy_generate cache from forever for cacheCut

def missingRank : VC.Specification Unit := { partialLoop with mode := .totalCorrectness }

/-- error: total correctness with cutpoints requires a ranking function; set Specification.ranking -/
#guard_msgs in
veripy_generate unranked from forever for missingRank

def constantRank : VC.Specification Unit :=
  { missingRank with ranking := some (fun _ _ _ => 0) }

#guard_msgs (drop info, all) in
veripy_generate totalGoals from forever for constantRank unfolding [missingRank, partialLoop]

example : ¬ totalGoals.VC.cut2 := by simp [totalGoals.VC.cut2]

-- Failures after generation has started also roll back published declarations.
def collision.VC.init : Prop := True

/-- error: (kernel) constant has already been declared 'VeriPyAsm.Tests.VCGeneration.collision.VC.init' -/
#guard_msgs in
veripy_generate collision from adder for addition

def projectionCollision.Proofs.entry : Nat := 1

/--
error: `VeriPyAsm.Tests.VCGeneration.projectionCollision.Proofs.entry` has already been declared
---
error: generated proof structure failed to elaborate; no VC manifest exported
-/
#guard_msgs in
veripy_generate projectionCollision from adder for addition

-- A malicious simplification lemma cannot turn a false safety condition into
-- checked evidence. The axiom fixture exists only in this temporary environment.
run_cmd do
  let environment ← getEnv
  try
    liftCoreM <| VC.addCheckedDeclaration (.axiomDecl {
      name := `VCGenerationFixture.false_is_true, levelParams := [], isUnsafe := false,
      type := mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero)
        (mkConst ``False) (mkConst ``True) })
    elabCommand (← `(command| attribute [simp] $(mkIdent `VCGenerationFixture.false_is_true)))
    let rejected ← try
      VC.elabGenerate (← `(command| veripy_generate $(mkIdent `untrusted)
        from $(mkIdent ``adder) for $(mkIdent ``faulty)))
      pure false
    catch error =>
      let detail ← error.toMessageData.toString
      unless detail.contains "unapproved axioms [VCGenerationFixture.false_is_true]" do
        throw error
      pure true
    unless rejected do throwError "generation accepted an unapproved normalization axiom"
  finally
    setEnv environment

-- Discovery exports complete parseable generated statements and metadata.
#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from totalGoals

example : pending.report.complete = false := rfl
example : pending.report.obligations[2]!.offset = 2 := rfl
example : pending.report.obligations[2]!.kind = "preservation_and_ranking" := rfl

run_cmd liftTermElabM do
  let manifest ← VC.getManifest ``Triangular.generated
  for obligation in manifest.obligations do
    let statement ← VC.goalStatement obligation.goal
    let .ok parsed := Parser.runParserCategory (← getEnv) `term statement
      | throwError "unparseable generated VC: {statement}"
    let expression ← Term.elabType parsed
    Term.synthesizeSyntheticMVarsNoPostponing
    unless (← isDefEq expression (mkConst obligation.goal)) do
      throwError "generated VC handoff changed its statement"
    discard <| VC.audit (obligation.goal ++ `normalization) .checked

#eval show CoreM Unit from do
  if (← getEnv).contains `VCGenerationFixture.false_is_true then
    throwError "untrusted normalization fixture escaped its temporary environment"
  for name in [`uncovered, `duplicate, `cache, `unranked] do
    for suffix in [Name.anonymous, `program, `VC.entry, `assemble, `Proofs] do
      let full := `VeriPyAsm.Tests.VCGeneration ++ name ++ suffix
      if (← getEnv).contains full then throwError "failed generation retained {full}"
  for name in [`collision, `projectionCollision, `untrusted] do
    for suffix in [Name.anonymous, `program, `VC.entry, `assemble, `Proofs] do
      let full := `VeriPyAsm.Tests.VCGeneration ++ name ++ suffix
      if (← getEnv).contains full then throwError "failed generation retained {full}"
  unless (← getEnv).contains `VeriPyAsm.Tests.VCGeneration.collision.VC.init do
    throwError "generation removed a preexisting declaration"
  unless (← getEnv).contains `VeriPyAsm.Tests.VCGeneration.projectionCollision.Proofs.entry do
    throwError "generation removed a preexisting projection name"

#veripy_audit VeriPyAsm.Tests.VCGeneration

end VeriPyAsm.Tests.VCGeneration
