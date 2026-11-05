import VeriPyAsm.Verification.Contract
import VeriPyAsm.Embedding

/-! Contract statements anchored to raw artifacts via successful decoding.
The translation's checked step equality transports correctness in both directions.
These judgments state semantic correctness under the contract precondition;
stack admission is a separate certificate, required by the verification workflow.
Neither judgment authenticates extraction or proves CPython runtime refinement. -/

namespace VeriPyAsm.Verification

open Semantics CPython.V314

universe u

def ArtifactPartialCorrect {Ghost : Type u} (artifact : Artifact)
    (contract : Contract Ghost) : Prop :=
  ∃ code, decode artifact = .ok code ∧ PartialCorrect (referenceStep code) contract

def ArtifactTotalCorrect {Ghost : Type u} (artifact : Artifact)
    (contract : Contract Ghost) : Prop :=
  ∃ code, decode artifact = .ok code ∧ TotalCorrect (referenceStep code) contract

theorem ArtifactTotalCorrect.to_partial {Ghost : Type u} {artifact : Artifact}
    {contract : Contract Ghost} (correct : ArtifactTotalCorrect artifact contract) :
    ArtifactPartialCorrect artifact contract := by
  obtain ⟨code, decoded, total⟩ := correct
  exact ⟨code, decoded, total.partialCorrect⟩

end VeriPyAsm.Verification

namespace VeriPyAsm.Embedding

open Semantics CPython.V314 Verification

universe u
variable {Ghost : Type u} {artifact : Artifact} (translation : Translation artifact)
    {contract : Contract Ghost}

theorem Translation.partial_correct_iff :
    PartialCorrect (step translation.program) contract ↔
      PartialCorrect (referenceStep translation.code) contract := by
  rw [translation.correct]

theorem Translation.total_correct_iff :
    TotalCorrect (step translation.program) contract ↔
      TotalCorrect (referenceStep translation.code) contract := by
  rw [translation.correct]

/-- Decoding is functional: a different witness cannot change the artifact's code. -/
theorem Translation.artifact_partial_iff :
    ArtifactPartialCorrect artifact contract ↔
      PartialCorrect (step translation.program) contract := by
  constructor
  · rintro ⟨code, decoded, correct⟩
    have equal := Except.ok.inj (decoded.symm.trans translation.decoded)
    cases equal
    exact translation.partial_correct_iff.mpr correct
  · intro correct
    exact ⟨translation.code, translation.decoded, translation.partial_correct_iff.mp correct⟩

theorem Translation.artifact_total_iff :
    ArtifactTotalCorrect artifact contract ↔
      TotalCorrect (step translation.program) contract := by
  constructor
  · rintro ⟨code, decoded, correct⟩
    have equal := Except.ok.inj (decoded.symm.trans translation.decoded)
    cases equal
    exact translation.total_correct_iff.mpr correct
  · intro correct
    exact ⟨translation.code, translation.decoded, translation.total_correct_iff.mp correct⟩

end VeriPyAsm.Embedding
