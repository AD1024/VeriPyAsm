import VeriPyAsm.Admission
import VeriPyAsm.Verification.Artifact

/-! Final verification packages combine admission, the contract's entry domain,
and semantic correctness. The lower-level artifact judgments deliberately remain
available, but cannot supply a missing certificate or entry proof. Runtime and
extraction correspondence remain outside this package's semantic guarantee. -/

namespace VeriPyAsm.Verification

open Semantics CPython.V314

universe u

/-- Ordinary call entry: positional arguments initialize the argument slots;
all other locals start unbound. Decoding checks argCount fits localNames. -/
def EntryFrame (artifact : Artifact) (initial : Frame) : Prop :=
  initial.pc = 0 ∧ initial.stack = [] ∧
    ∃ arguments : List Value, arguments.length = artifact.argCount ∧
      initial.locals = arguments.map some ++
        List.replicate (artifact.localNames.length - artifact.argCount) none

theorem EntryFrame.eq_entry {artifact : Artifact} {initial : Frame}
    (entry : EntryFrame artifact initial) : initial = { locals := initial.locals } := by
  rcases initial with ⟨pc, locals, stack⟩
  rcases entry with ⟨rfl, rfl, _⟩
  rfl

inductive CorrectnessMode where
  | partialCorrectness
  | totalCorrectness

def CorrectnessMode.Judgment {Ghost : Type u} (mode : CorrectnessMode)
    (next : Frame → StepResult) (contract : Contract Ghost) : Prop :=
  match mode with
  | .partialCorrectness => PartialCorrect next contract
  | .totalCorrectness => TotalCorrect next contract

/-- A final result cannot omit stack/ownership certificates or silently restrict
the contract's precondition to the certificate's entry assumptions. -/
structure VerifiedArtifact {Ghost : Type u} (artifact : Artifact)
    (contract : Contract Ghost) (mode : CorrectnessMode := .totalCorrectness) where
  admission : Admitted artifact
  entry : ∀ ghost initial, contract.pre ghost initial → EntryFrame artifact initial
  correctness : mode.Judgment (step admission.translation.program) contract

variable {Ghost : Type u} {artifact : Artifact} {contract : Contract Ghost}
    {mode : CorrectnessMode}

theorem VerifiedArtifact.partialCorrect (verified : VerifiedArtifact artifact contract mode) :
    PartialCorrect (step verified.admission.translation.program) contract := by
  cases mode with
  | partialCorrectness => exact verified.correctness
  | totalCorrectness => exact verified.correctness.partialCorrect

theorem VerifiedArtifact.artifact_partial (verified : VerifiedArtifact artifact contract mode) :
    ArtifactPartialCorrect artifact contract :=
  verified.admission.translation.artifact_partial_iff.mpr verified.partialCorrect

theorem VerifiedArtifact.artifact_total (verified : VerifiedArtifact artifact contract) :
    ArtifactTotalCorrect artifact contract :=
  verified.admission.translation.artifact_total_iff.mpr verified.correctness

def VerifiedArtifact.to_partial (verified : VerifiedArtifact artifact contract) :
    VerifiedArtifact artifact contract .partialCorrectness :=
  ⟨verified.admission, verified.entry, verified.correctness.partialCorrect⟩

theorem VerifiedArtifact.entry_matches (verified : VerifiedArtifact artifact contract mode)
    {ghost : Ghost} {initial : Frame} (pre : contract.pre ghost initial) :
    verified.admission.stack.Matches initial := by
  have entry := verified.entry ghost initial pre
  change Stack.heightAt verified.admission.stack.heights initial.pc = some initial.stack.length
  rw [entry.1, entry.2.1]
  exact verified.admission.stack.valid.1

/-- Certificate guarantees apply to every contract pre-state, rather than only
to a separately assumed canonical initial frame. -/
theorem VerifiedArtifact.run_exhausted_bound (verified : VerifiedArtifact artifact contract mode)
    {ghost : Ghost} {initial current : Frame} {fuel : Nat}
    (pre : contract.pre ghost initial)
    (execution : run (step verified.admission.translation.program) fuel initial = .exhausted current) :
    current.stack.length ≤ artifact.stackSize := by
  rw [verified.admission.translation.correct] at execution
  exact verified.admission.stack.run_exhausted_bound fuel initial current
    (verified.entry_matches pre) execution

theorem VerifiedArtifact.reachable_ownership (verified : VerifiedArtifact artifact contract mode)
    {ghost : Ghost} {initial current : Frame} (pre : contract.pre ghost initial)
    (path : Reaches (step verified.admission.translation.program) initial current) :
    ∃ refs instruction output,
      Ownership.Path verified.admission.translation.code 0 [] current.pc refs ∧
      fetch verified.admission.translation.code.instructions current.pc = some instruction ∧
      Ownership.transfer instruction.op refs = .ok output := by
  rw [(verified.entry ghost initial pre).eq_entry] at path
  exact verified.admission.reachable_ownership initial.locals path

end VeriPyAsm.Verification
