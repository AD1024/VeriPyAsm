import VeriPyAsm.Examples.Triangular.Manifest
import VeriPyAsm.Automation.Crush
import VeriPyAsm.Verification.AxiomAudit

/-! Checked Crush proofs of the actual triangular VCs and their assembly into
total correctness of the imported artifact. The ordinary arithmetic provider
is not imported. Build separately with `lake build TriangularCrush` and cvc5
on PATH; the core library does not require an installed solver. -/

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.timeout 5
set_option crush.reconstruct.trustBvDecide false
set_option crush.reconstruct.trustNativeDecide false

namespace VeriPyAsm.Examples.Triangular.CrushProofs

open Verification

/-- Normalize the Nat rank comparison to Int before invoking Crush. A direct
call on the `toNat` comparison returned `unknown` in the initial experiment. -/
@[veripy_proof VC.loop6.decrease]
theorem decrease : VC.loop6.decrease := by
  intro n positive
  rw [Int.toNat_lt_toNat positive]
  crush

-- Resolve the registered ranking proof first; automatically discharge the
-- other three VCs with Crush, then assemble and audit the final artifact package.
veripy_verify verified from obligations

theorem init : VC.loop6.init := verified.vc.init
theorem preserve : VC.loop6.preserve := verified.vc.preserve
theorem exit : VC.loop6.exit := verified.vc.exit

theorem proofs : VC.Proofs where
  init := init
  preserve := preserve
  exit := exit
  decrease := decrease

theorem artifact_total : ArtifactTotalCorrect triangularArtifact triangularContract :=
  Assembly.artifact_total proofs

example : verified.report.complete = true := rfl
example : verified.report.assurance = some "checked" := rfl
example : verified.report.obligations[0]!.provider = "crush" := rfl
example : verified.report.obligations[1]!.provider = "crush" := rfl
example : verified.report.obligations[2]!.provider = "crush" := rfl
example : verified.report.obligations[3]!.provider = "manual" := rfl

-- This check fails the build if reconstruction introduces any nonstandard axiom.
#eval show Lean.CoreM Unit from do
  if (← Lean.getEnv).contains `VeriPyAsm.Examples.Triangular.Arithmetic.proofs then
    throwError "The Crush provider unexpectedly imports the ordinary arithmetic proofs"

#veripy_audit VeriPyAsm.Examples.Triangular.CrushProofs

#print axioms init
#print axioms preserve
#print axioms exit
#print axioms decrease
#print axioms artifact_total

end VeriPyAsm.Examples.Triangular.CrushProofs
