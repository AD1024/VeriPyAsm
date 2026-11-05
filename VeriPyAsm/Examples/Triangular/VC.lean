import Init

/-! Closed residual verification conditions for the imported triangular loop.

These propositions are extracted by hand from the proved bytecode summaries.
`Assembly.lean` proves that supplying all four suffices for the artifact contract;
this module neither proves them nor imports a proof provider. The `loop6` names
refer to the invariant cutpoint at byte offset 6. -/

namespace VeriPyAsm.Examples.Triangular.VC

namespace loop6

/-- Entry path 0 → 6: initialize the invariant's equation with sum = 0. -/
def init : Prop :=
  ∀ N : Int, 2 * 0 + N * (N + 1) = N * (N + 1)

/-- Body path 6 → 20 → 6: preserve the equation after updating both locals. -/
def preserve : Prop :=
  ∀ N n sum : Int, 2 * sum + n * (n + 1) = N * (N + 1) →
    2 * (sum + n) + (n - 1) * ((n - 1) + 1) = N * (N + 1)

/-- Exit path 6 → 58: establish both the final counter and return equation. -/
def exit : Prop :=
  ∀ N n sum : Int, 0 ≤ n → n ≤ 0 →
    2 * sum + n * (n + 1) = N * (N + 1) →
    n = 0 ∧ 2 * sum = N * (N + 1)

/-- Back edge to 6: preserve nonnegativity and strictly decrease the Nat rank. -/
def decrease : Prop :=
  ∀ n : Int, 0 < n → 0 ≤ n - 1 ∧ (n - 1).toNat < n.toNat

end loop6

/-- Every residual obligation is an explicit proof premise, including decrease.
Instruction safety and finite iteration execution are already proved in Blocks. -/
structure Proofs : Prop where
  init : loop6.init
  preserve : loop6.preserve
  exit : loop6.exit
  decrease : loop6.decrease

end VeriPyAsm.Examples.Triangular.VC
