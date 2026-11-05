import VeriPyAsm.Automation.Crush
import VeriPyAsm.Examples.Add1

/-! Integration regressions for the optional adapter. Real cvc5 exercises checked
reconstruction, sat/pending, and explicit solver trust. Trusted test declarations
exist only in restored temporary environments and never enter the checked library.
-/

namespace VeriPyAsm.Tests.VCDischargeCrush

open Lean Meta Elab Command Verification
open Verification.VC Examples

def impossible : Prop := False
def arithmetic : Prop := ∀ n : Int, n + 1 > n
def supplied : Prop := ∀ n : Int, n = n

structure MixedProofs : Prop where
  first : impossible
  second : arithmetic
  third : supplied

def mixedAssembly (_proofs : MixedProofs) : VerifiedArtifact add1Artifact add1Contract := add1_verified

veripy_vcs mixed : VerifiedArtifact add1Artifact add1Contract via mixedAssembly where
  first : impossible at 0 vc_kind "test_failure"
  second : arithmetic at 2 vc_kind "test_success"
  third : supplied at 4 vc_kind "test_override"

@[veripy_proof supplied]
theorem manual : supplied := fun _ => rfl

-- The adapter overrides these unsafe ambient settings in checked mode.
set_option crush.trust "trust"
set_option crush.reconstruct.trustNativeDecide true
set_option crush.reconstruct.trustBvDecide true

#guard_msgs (drop info, all) in
veripy_discover discovered from mixed

example : discovered.report.complete = false := rfl
example : discovered.report.obligations[0]!.failureKind = some "sat" := rfl
example : discovered.report.obligations[0]!.actualBackend = some "cvc5" := rfl
example : discovered.report.obligations[1]!.status = "proved" := rfl
example : discovered.report.obligations[1]!.assurance = some "checked" := rfl
example : discovered.report.obligations[2]!.provider = "manual" := rfl

/-- error: verification incomplete: 1 unresolved VC(s); no VerifiedArtifact exported -/
#guard_msgs (drop info, all) in
veripy_verify rejected from mixed

#eval show CoreM Unit from do
  if (← getEnv).contains `VeriPyAsm.Tests.VCDischargeCrush.rejected then
    throwError "an incomplete verification exported a package"

structure ArithmeticProofs : Prop where
  result : arithmetic

def arithmeticAssembly (_proofs : ArithmeticProofs) : VerifiedArtifact add1Artifact add1Contract := add1_verified

veripy_vcs arithmeticManifest : VerifiedArtifact add1Artifact add1Contract via arithmeticAssembly where
  result : arithmetic at 2 vc_kind "arithmetic"

-- Test real solver trust and registration policy enforcement without exporting
-- trusted declarations into the checked regression namespace.
#guard_msgs (drop info, all) in
run_cmd do
  let environment ← getEnv
  try
    let manifest ← liftCoreM <| getManifest ``arithmeticManifest
    let report ← runManifest manifest `TrustedFixture.verified true { policy := .solver_trusted }
    unless report.complete && report.assurance == some "solver_trusted" &&
        report.obligations[0]!.axioms.contains "Crush.crushSorry" &&
        report.obligations[0]!.actualBackend == some "cvc5" do
      throwError "explicit trust did not record actual solver/axiom evidence"
    let theoremName := `TrustedFixture.verified.vc.result
    liftCoreM <| registerProof theoremName ``arithmetic .solver_trusted
    let checked ← runManifest manifest `TrustedFixture.checked false {}
    unless checked.obligations[0]!.failureKind == some "registration_rejected" &&
        checked.obligations[0]!.provider == "manual" &&
        checked.obligations[0]!.detail.contains "Crush.crushSorry" do
      throwError "checked mode silently ignored an invalid manual override"
    let trusted ← runManifest manifest `TrustedFixture.manual true { policy := .solver_trusted }
    unless trusted.assurance == some "solver_trusted" &&
        trusted.obligations[0]!.provider == "manual" do
      throwError "manual labels upgraded solver-trusted evidence"
  finally
    setEnv environment

-- Stable classifications retain raw diagnostics for unrecognized backend errors.
#eval show IO Unit from do
  for (diagnostic, expected) in [
      ("crush: solver returned `unknown` (incomplete). Try increasing `crush.timeout`.", "unknown"),
      ("crush: solver returned `unknown` (timeout)", "timeout"),
      ("crush: unsupported translation", "unsupported_translation"),
      ("crush: reconstruction failed", "reconstruction_failed")] do
    unless Automation.Crush.failureKind diagnostic == expected do
      throw <| IO.userError s!"incorrect classification for {diagnostic}"

#veripy_audit VeriPyAsm.Tests.VCDischargeCrush

end VeriPyAsm.Tests.VCDischargeCrush
