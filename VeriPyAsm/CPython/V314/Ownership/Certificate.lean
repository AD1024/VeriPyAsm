import VeriPyAsm.CPython.V314.Ownership.Rules

/-! Independently checked ownership tables. Entries record the origin of every
stack slot, not just its height. Both branch edges and back edges must preserve
the exact stack provenance. Conflicting joins are conservatively rejected. -/

namespace VeriPyAsm.CPython.V314.Ownership

abbrev Table := List (Nat × Stack)

def stackAt : Table → Nat → Option Stack
  | [], _ => none
  | (offset, refs) :: rest, pc => if pc = offset then some refs else stackAt rest pc

def RowValid (code : Code) (table : Table) (row : Nat × Stack) : Prop :=
  match fetch code.instructions row.1 with
  | none => False
  | some instruction =>
    match transfer instruction.op row.2 with
    | .error _ => False
    | .ok output => ∀ target ∈ instruction.successors, stackAt table target = some output

instance (code : Code) (table : Table) (row : Nat × Stack) :
    Decidable (RowValid code table row) := by
  unfold RowValid
  split
  · infer_instance
  · split <;> infer_instance

def Valid (code : Code) (table : Table) : Prop :=
  stackAt table 0 = some [] ∧ table.Pairwise (fun a b => a.1 ≠ b.1) ∧
    ∀ row ∈ table, RowValid code table row

instance (code : Code) (table : Table) : Decidable (Valid code table) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Certificate (code : Code) where
  table : Table
  valid : Valid code table

def check (code : Code) (table : Table) : Option (Certificate code) :=
  if h : Valid code table then some ⟨table, h⟩ else none

end VeriPyAsm.CPython.V314.Ownership
