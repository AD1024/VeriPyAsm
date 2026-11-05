import Crush
import VeriPyAsm.Verification.AxiomAudit

/-!
# Candidate verification conditions for VeriPyAsm

These stand-alone propositions exercise the proposed automation boundary. They
are not generated from bytecode and do not prove a Python function correct.

This file is a separate Lake library target. Run `lake build CrushObligations`
to check it against the pinned Crush dependency; see `docs/CRUSH.md`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.timeout 5
set_option crush.reconstruct.trustBvDecide false
set_option crush.reconstruct.trustNativeDecide false

namespace VeriPyAsm.CrushExperiment

/-- Arithmetic side condition for a decreasing nonnegative loop counter. -/
theorem ranking (n : Int) (h : 0 < n) : 0 ≤ n - 1 ∧ n - 1 < n := by
  crush

/-- Initializing the triangular-number loop invariant with `s = 0`. -/
theorem invariantInit (n : Int) : 2 * 0 + n * (n + 1) = n * (n + 1) := by
  crush

/-- Preserving the mathematical invariant through one loop body. -/
theorem invariantStep (initial n s : Int)
    (h : 2 * s + n * (n + 1) = initial * (initial + 1)) :
    2 * (s + n) + (n - 1) * ((n - 1) + 1) = initial * (initial + 1) := by
  crush

/-- Deriving the result equation when the nonnegative counter reaches zero. -/
theorem invariantExit (initial n s : Int) (hn : 0 ≤ n) (hexit : n ≤ 0)
    (h : 2 * s + n * (n + 1) = initial * (initial + 1)) :
    2 * s = initial * (initial + 1) := by
  crush

/-- A functional-update side condition; this is not a Python heap model. -/
theorem frameCondition (before after : Nat → Int) (i j : Nat) (value : Int)
    (update : ∀ k, after k = if k = i then value else before k) (distinct : j ≠ i) :
    after j = before j := by
  crush

#print axioms ranking
#print axioms invariantInit
#print axioms invariantStep
#print axioms invariantExit
#print axioms frameCondition

end VeriPyAsm.CrushExperiment

#veripy_audit VeriPyAsm.CrushExperiment
