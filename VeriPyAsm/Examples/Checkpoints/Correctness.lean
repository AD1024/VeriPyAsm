import VeriPyAsm.Examples.Checkpoints.Segments
import VeriPyAsm.Verification.VC.Discharge

namespace VeriPyAsm.Examples.Checkpoints

open Verification

@[veripy_proof VC.entry]
theorem entry : VC.entry := Segments.entry

@[veripy_proof VC.runtimeAssertion]
theorem runtimeAssertion : VC.runtimeAssertion := Segments.runtimeAssertion

@[veripy_proof VC.hint]
theorem hint : VC.hint := by
  intro n nonnegative
  omega

@[veripy_proof VC.finish]
theorem finish : VC.finish := Segments.finish

set_option veripy.auto false in
veripy_verify verified from obligations

theorem artifact_total : ArtifactTotalCorrect Assertions.nonnegativeArtifact contract :=
  verified.artifact_total

#veripy_audit VeriPyAsm.Examples.Checkpoints

end VeriPyAsm.Examples.Checkpoints
