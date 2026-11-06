import VeriPyAsm.Examples.Assertions.Generated
import VeriPyAsm.Verification.VC.Discharge

/-! Checked total-correctness packages for both assertion contracts. Their
execution VCs normalize to True: the branch conditions establish precisely the
normal or exceptional postcondition. Entry compatibility remains explicit. -/

namespace VeriPyAsm.Examples.Assertions

open Verification

namespace ExceptionFree

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n _
  exact ⟨[.int n], rfl, rfl⟩

@[veripy_proof generated.VC.init]
theorem execution : generated.VC.init := True.intro

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : ArtifactTotalCorrect nonnegativeArtifact contract := verified.artifact_total

end ExceptionFree

namespace WithFailure

@[veripy_proof generated.VC.entry]
theorem entry : generated.VC.entry := by
  intro n
  exact ⟨[.int n], rfl, rfl⟩

@[veripy_proof generated.VC.init]
theorem execution : generated.VC.init := True.intro

set_option veripy.auto false in
veripy_verify verified from generated

theorem artifact_total : ArtifactTotalCorrect nonnegativeArtifact contract := verified.artifact_total

end WithFailure

#veripy_audit VeriPyAsm.Examples.Assertions

end VeriPyAsm.Examples.Assertions
