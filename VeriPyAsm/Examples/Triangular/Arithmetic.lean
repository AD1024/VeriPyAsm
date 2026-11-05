import Init

/-! Mathematical obligations for the triangular loop, independent of bytecode,
frames, and proof automation packages. Lean reconstructs the arithmetic proofs. -/

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

end VeriPyAsm.Examples.Triangular.Arithmetic
