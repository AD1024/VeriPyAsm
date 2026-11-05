import VeriPyAsm.Examples.Add1
import VeriPyAsm.Examples.Triangular

/-! Admission and entry compatibility are mandatory in the public package.
The lower-level judgments remain useful, with strictly weaker requirements. -/

namespace VeriPyAsm.Tests.VerifiedArtifact

open Semantics CPython.V314 Verification Examples

example : Verification.VerifiedArtifact add1Artifact add1Contract := add1_verified
example : Verification.VerifiedArtifact triangularArtifact triangularContract := triangular_verified
example : Verification.VerifiedArtifact triangularArtifact triangularContract .partialCorrectness :=
  triangular_verified.to_partial
example : ArtifactTotalCorrect triangularArtifact triangularContract := triangular_verified.artifact_total

private def undersizedArtifact : Artifact := { add1Artifact with stackSize := 0 }
private def undersized : Embedding.Translation undersizedArtifact := bytecode% undersizedArtifact

-- The review's lower-level correctness proof is still legitimate.
theorem undersized_model_correct : ArtifactTotalCorrect undersizedArtifact add1Contract :=
  undersized.artifact_total_iff.mpr add1_contract_total

-- Yet no possible admission certificate can package it as verified: every
-- certificate would bound this reachable one-item stack by the declared zero.
theorem undersized_not_verified :
    ¬ Nonempty (Verification.VerifiedArtifact undersizedArtifact add1Contract) := by
  rintro ⟨verified⟩
  have same := Except.ok.inj
    (verified.admission.translation.decoded.symm.trans undersized.decoded)
  have execution : run (step verified.admission.translation.program) 2
      { locals := [some (.int 0)] } =
      .exhausted { pc := 4, locals := [some (.int 0)], stack := [.int 0] } := by
    rw [verified.admission.translation.correct, same]
    decide +kernel
  have bound := verified.run_exhausted_bound (ghost := 0) rfl execution
  exact Nat.not_succ_le_zero 0 bound

private def midProgramContract : Contract Unit where
  pre _ initial := initial = { pc := 18, locals := [some (.int 0)], stack := [.int 7] }
  post _ _ value _ := value = .int 7
  raises _ _ _ _ := False

theorem mid_program_model_correct : ArtifactTotalCorrect add1Artifact midProgramContract := by
  apply add1Admitted.translation.artifact_total_iff.mpr
  apply TotalCorrect.of_run
  rintro _ initial rfl
  exact ⟨1, .returned (.int 7) { pc := 18, locals := [some (.int 0)] }, rfl, rfl⟩

theorem mid_program_not_verified :
    ¬ Nonempty (Verification.VerifiedArtifact add1Artifact midProgramContract) := by
  rintro ⟨verified⟩
  have entry := verified.entry () _ rfl
  have impossible : (18 : Nat) = 0 := entry.1
  cases impossible

-- Each entry assumption is explicit, including local initialization.
example : ¬ EntryFrame add1Artifact { locals := [some (.int 0)], stack := [.int 7] } := by
  intro entry
  cases entry.2.1

example : ¬ EntryFrame add1Artifact { locals := [none] } := by
  rintro ⟨_, _, arguments, length, locals⟩
  cases arguments with
  | nil => cases length
  | cons value rest => simp at locals

example : ¬ EntryFrame triangularArtifact { locals := [some (.int 0), some (.int 7)] } := by
  rintro ⟨_, _, arguments, length, locals⟩
  have len : arguments.length = 1 := length
  cases arguments with
  | nil => cases len
  | cons value rest =>
    have empty : rest = [] := by cases rest <;> simp_all
    subst rest
    simp [triangularArtifact, add1Artifact] at locals

example : True := by
  fail_if_success
    have _ : Verification.VerifiedArtifact undersizedArtifact add1Contract := add1_verified
  trivial

#print axioms add1_verified
#print axioms triangular_verified
#print axioms undersized_not_verified
#print axioms mid_program_not_verified

end VeriPyAsm.Tests.VerifiedArtifact
