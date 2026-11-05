import VeriPyAsm.Examples.Triangular.Assembly
import VeriPyAsm.Verification.AxiomAudit

/-! The conditional assembly is usable without either proof provider. Check
the exact closed propositions, require all four premises, and audit assumptions. -/

namespace VeriPyAsm.Tests.VCAssembly

open Verification Examples Examples.Triangular

-- These are statement-identity checks, not proofs by logical equivalence.
example : VC.loop6.init =
    (∀ N : Int, 2 * 0 + N * (N + 1) = N * (N + 1)) := rfl

example : VC.loop6.preserve =
    (∀ N n sum : Int, 2 * sum + n * (n + 1) = N * (N + 1) →
      2 * (sum + n) + (n - 1) * ((n - 1) + 1) = N * (N + 1)) := rfl

example : VC.loop6.exit =
    (∀ N n sum : Int, 0 ≤ n → n ≤ 0 →
      2 * sum + n * (n + 1) = N * (N + 1) →
      n = 0 ∧ 2 * sum = N * (N + 1)) := rfl

example : VC.loop6.decrease =
    (∀ n : Int, 0 < n → 0 ≤ n - 1 ∧ (n - 1).toNat < n.toNat) := rfl

theorem conditional_artifact (init : VC.loop6.init) (preserve : VC.loop6.preserve)
    (exit : VC.loop6.exit) (decrease : VC.loop6.decrease) :
    ArtifactTotalCorrect triangularArtifact triangularContract :=
  Assembly.artifact_total { init, preserve, exit, decrease }

-- Neither a missing ranking proof nor a logically equivalent reordered type
-- is accepted as an exact instance of the VC interface.
example (_init : VC.loop6.init) (_preserve : VC.loop6.preserve) (_exit : VC.loop6.exit) :
    True := by
  fail_if_success
    have incomplete : VC.Proofs := { init := _init, preserve := _preserve, exit := _exit }
  trivial

example : True := by
  fail_if_success
    have reordered : VC.loop6.decrease =
        (∀ n : Int, 0 < n → (n - 1).toNat < n.toNat ∧ 0 ≤ n - 1) := rfl
  trivial

-- Guard the import boundary as well as the proof's transitive axioms.
#eval show Lean.CoreM Unit from do
  let environment ← Lean.getEnv
  for name in [`VeriPyAsm.Examples.Triangular.Arithmetic.proofs,
      `VeriPyAsm.Examples.triangular_total, `Crush.crushSorry] do
    if environment.contains name then
      throwError "Conditional assembly unexpectedly imports {name}"

#veripy_audit VeriPyAsm

#print axioms Assembly.artifact_total
#print axioms conditional_artifact

end VeriPyAsm.Tests.VCAssembly
