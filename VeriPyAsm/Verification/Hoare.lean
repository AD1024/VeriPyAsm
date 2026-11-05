import VeriPyAsm.Verification.Contract

/-! Scoped Hoare notation for normal-return contracts over machine frames.

Open `VeriPyAsm.Verification.Hoare` to write `{ P } S { Q }` for partial
correctness and `{{ P }} S {{ Q }}` for total correctness. `S` is a `Program`;
`P` and `Q` are `Frame → Prop`, so either can inspect `.stack` and `.locals`.
Program applications must be parenthesized, e.g. `(Embedding.compile code)`.

The postcondition observes the actual frame after normal return; RETURN_VALUE
has already popped the returned value. Both forms exclude Python exceptions and
VM faults. Use `Contract` directly for returned values, relational initial/final
conditions, explicit ghost parameters, or permitted Python exceptions.

These expand definitionally to the existing correctness predicates. They create
Lean propositions, not proofs or a verification-condition generation pass.
They concern whole-program execution, not a single instruction or block. -/

namespace VeriPyAsm.Verification

open Semantics

/-- Lift frame predicates to a contract with no permitted exceptional exit.
Outer theorem binders can retain logical inputs for both predicates. -/
def Contract.ofFramePredicates (pre post : Frame → Prop) : Contract Unit where
  pre _ := pre
  post _ _ _ := post
  raises _ _ _ _ := False

namespace Hoare

scoped notation:max "{ " P " } " S:max " { " Q " }" =>
  PartialCorrect (step S) (Contract.ofFramePredicates P Q)

scoped notation:max "{{ " P " }} " S:max " {{ " Q " }}" =>
  TotalCorrect (step S) (Contract.ofFramePredicates P Q)

end Hoare
end VeriPyAsm.Verification
