import VeriPyAsm.CPython.V314.Language

/-! Conservative reference-lifetime rules for the supported scalar instructions.
The stack head is the top. A borrowed slot depends on an unchanged local; an
owned slot has no local dependency (this includes immortal scalar references).
Locals never receive borrowed slots in this profile. These rules model CPython's
borrowing protocol, not its allocator or reference-count implementation.

See CPython v3.14.4 Python/flowgraph.c:2574-2608 and Python/bytecodes.c. -/

namespace VeriPyAsm.CPython.V314.Ownership

inductive Reference where
  | owned
  | borrowed (index : Nat)
  deriving Repr, DecidableEq

abbrev Stack := List Reference

inductive Violation where
  | underflow
  | storeBorrow (source destination : Nat)
  | overwriteBorrowed (index : Nat)
  deriving Repr, DecidableEq

def Violation.message : Violation → String
  | .underflow => "ownership stack underflow"
  | .storeBorrow source destination =>
    s!"cannot store a borrow from local {source} into local {destination}"
  | .overwriteBorrowed index => s!"cannot overwrite local {index} while its borrow is live"

/-- Check before killing the supporting local. For fused stores the remaining
stack includes the next value to be stored, not just the final stack suffix. -/
def store (index : Nat) : Stack → Except Violation Stack
  | [] => .error .underflow
  | .borrowed source :: _ => .error (.storeBorrow source index)
  | .owned :: rest =>
    if .borrowed index ∈ rest then .error (.overwriteBorrowed index) else .ok rest

/-- Successful normal effects. Exceptional paths terminate in the current
handler-free model. RETURN_VALUE upgrades a live borrow before clearing locals.
Binary/comparison results and Boolean conversion have independent lifetimes. -/
def transfer : Op → Stack → Except Violation Stack
  | .resume, refs | .notTaken, refs | .jump _, refs => .ok refs
  | .loadConst _, refs | .loadSmallInt _, refs | .loadFast _, refs |
      .loadFastCheck _, refs => .ok (.owned :: refs)
  | .loadFastBorrow index, refs => .ok (.borrowed index :: refs)
  | .loadFastLoadFast _ _, refs => .ok (.owned :: .owned :: refs)
  | .loadFastBorrowLoadFastBorrow first second, refs =>
    .ok (.borrowed second :: .borrowed first :: refs)
  | .storeFast index, refs => store index refs
  | .storeFastLoadFast destination _, refs => do
    let rest ← store destination refs
    pure (.owned :: rest)
  | .storeFastStoreFast first second, refs => do
    let rest ← store first refs
    store second rest
  | .binary _, _ :: _ :: rest | .compare _, _ :: _ :: rest => .ok (.owned :: rest)
  | .toBool, _ :: rest => .ok (.owned :: rest)
  | .popJumpIfFalse .., _ :: rest | .popJumpIfTrue .., _ :: rest |
      .returnValue, _ :: rest => .ok rest
  | _, _ => .error .underflow

/-- A successful store neither installs a borrow nor invalidates a live one. -/
theorem store_safe {index : Nat} {before after : Stack}
    (success : store index before = .ok after) :
    before = .owned :: after ∧ .borrowed index ∉ after := by
  cases before with
  | nil => cases success
  | cons ref rest =>
    cases ref with
    | borrowed _ => cases success
    | owned =>
      simp only [store] at success
      split at success
      · contradiction
      · cases success
        exact ⟨rfl, by assumption⟩

end VeriPyAsm.CPython.V314.Ownership
