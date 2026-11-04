import VeriPyAsm.Semantics.Machine

/-! Atomic scalar semantics for CPython's fused local instructions. Stack order
and assignment order follow CPython 3.14.4 Python/bytecodes.c. Each command is
one transition; faults retain the instruction-entry snapshot, even when the
fault is detected after an internal lookup or proposed store.

The intermediate stack heights are bounded by the endpoints: a pair of loads
only grows the stack; store-load first removes then replaces its top; a pair of
stores only shrinks it. Thus input/output capacity checks suffice for these
particular fusions. Borrowing and reference ownership remain unobservable in
the exact-scalar profile. -/

namespace VeriPyAsm.Semantics.Command

/-- Read the first local before the second, leaving the second value on top. -/
def loadPair (next first second : Nat) : Command := fun s =>
  match s.locals[first]? with
  | none => .halted (.fault (.invalidLocal first) s)
  | some none => .halted (.fault (.unboundUncheckedLocal first) s)
  | some (some firstValue) =>
    match s.locals[second]? with
    | none => .halted (.fault (.invalidLocal second) s)
    | some none => .halted (.fault (.unboundUncheckedLocal second) s)
    | some (some secondValue) =>
      .next { s with pc := next, stack := secondValue :: firstValue :: s.stack }

/-- Store before reloading: equal indices must load the newly stored value. -/
def storeLoad (next storeIndex loadIndex : Nat) : Command := fun s =>
  if storeIndex ≥ s.locals.length then .halted (.fault (.invalidLocal storeIndex) s)
  else match s.stack with
    | [] => .halted (.fault .stackUnderflow s)
    | value :: rest =>
      let locals := s.locals.set storeIndex (some value)
      match locals[loadIndex]? with
      | none => .halted (.fault (.invalidLocal loadIndex) s)
      | some none => .halted (.fault (.unboundUncheckedLocal loadIndex) s)
      | some (some loaded) =>
        .next { s with pc := next, locals, stack := loaded :: rest }

/-- Store the top at the first index, then the next value at the second index.
When indices coincide, the second assignment wins. -/
def storePair (next first second : Nat) : Command := fun s =>
  if first ≥ s.locals.length then .halted (.fault (.invalidLocal first) s)
  else if second ≥ s.locals.length then .halted (.fault (.invalidLocal second) s)
  else match s.stack with
    | top :: below :: rest =>
      let locals := (s.locals.set first (some top)).set second (some below)
      .next { s with pc := next, locals, stack := rest }
    | _ => .halted (.fault .stackUnderflow s)

end VeriPyAsm.Semantics.Command
