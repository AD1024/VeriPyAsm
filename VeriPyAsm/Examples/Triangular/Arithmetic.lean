import VeriPyAsm.Examples.Triangular.VC

/-! Ordinary Lean proofs of the closed triangular VCs, independent of bytecode,
frames, and external proof automation. This is one replaceable proof provider. -/

namespace VeriPyAsm.Examples.Triangular.Arithmetic

theorem at_entry (N : Int) : 2 * 0 + N * (N + 1) = N * (N + 1) := by omega

theorem preserve (N n sum : Int)
    (invariant : 2 * sum + n * (n + 1) = N * (N + 1)) :
    2 * (sum + n) + (n - 1) * ((n - 1) + 1) = N * (N + 1) := by
  grind

theorem at_exit (N n sum : Int) (nonnegative : 0 ≤ n) (nonpositive : n ≤ 0)
    (invariant : 2 * sum + n * (n + 1) = N * (N + 1)) :
    2 * sum = N * (N + 1) := by
  have zero : n = 0 := by omega
  subst n
  simpa using invariant

theorem decrease (n : Int) (positive : 0 < n) :
    0 ≤ n - 1 ∧ (n - 1).toNat < n.toNat := by omega

theorem exit : VC.loop6.exit := by
  intro N n sum nonnegative nonpositive invariant
  exact ⟨by omega, at_exit N n sum nonnegative nonpositive invariant⟩

theorem proofs : VC.Proofs where
  init := at_entry
  preserve := preserve
  exit := exit
  decrease := decrease

end VeriPyAsm.Examples.Triangular.Arithmetic
