import VeriPyAsm.CPython.V314.Stack.Rules

/-! Finite, independently checkable stack certificates. No worklist algorithm is
trusted here. A certificate contains entry height 0 and a closed set of normal
successors; unreachable instructions need not have entries. This checks heights,
not types, local initialization, termination, or Python exception freedom. -/

namespace VeriPyAsm.CPython.V314.Stack

abbrev Heights := List (Nat × Nat)

def heightAt : Heights → Nat → Option Nat
  | [], _ => none
  | (offset, height) :: rest, pc =>
    if pc = offset then some height else heightAt rest pc

/-- All successful control-flow edges must have the computed post-height. Input
and output capacity are checked explicitly, including terminal instructions. -/
def RowValid (code : Code) (capacity : Nat) (heights : Heights) (row : Nat × Nat) : Prop :=
  match fetch code.instructions row.1 with
  | none => False
  | some i =>
    i.StackReady row.2 ∧ row.2 ≤ capacity ∧ i.outputHeight row.2 ≤ capacity ∧
      ∀ target ∈ i.successors, heightAt heights target = some (i.outputHeight row.2)

instance (code : Code) (capacity : Nat) (heights : Heights) (row : Nat × Nat) :
    Decidable (RowValid code capacity heights row) := by
  unfold RowValid
  split <;> infer_instance

/-- The certificate's entire obligation, expressed as a decidable Lean proposition.
Duplicate offsets are rejected, even if their supplied heights happen to agree. -/
def Valid (code : Code) (capacity : Nat) (heights : Heights) : Prop :=
  heightAt heights 0 = some 0 ∧
    heights.Pairwise (fun a b => a.1 ≠ b.1) ∧
    ∀ row ∈ heights, RowValid code capacity heights row

instance (code : Code) (capacity : Nat) (heights : Heights) :
    Decidable (Valid code capacity heights) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Certificate (code : Code) (capacity : Nat) where
  heights : Heights
  valid : Valid code capacity heights

/-- Accept a proposed table only with a proof of the checker proposition. -/
def check (code : Code) (capacity : Nat) (heights : Heights) :
    Option (Certificate code capacity) :=
  if h : Valid code capacity heights then some ⟨heights, h⟩ else none

end VeriPyAsm.CPython.V314.Stack
