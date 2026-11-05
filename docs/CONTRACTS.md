# Sequential contracts and the first program proof

The current contract interface uses native Lean predicates. It supports partial
and total correctness for the deterministic scalar machine, including normal and
exceptional exits, with scoped Hoare notation for frame predicates. Sound
[instruction and block rules](RULES.md) support compositional proofs. It does not
yet provide a full specification DSL, loop rules, generated VCs, proof
registration, or solver discharge.

## Execution boundary

`Semantics/Execution.lean` separates two relations:

- `Reaches next initial current`: zero or more continuing transitions.
- `Executes next initial outcome`: continuing transitions followed by a terminal
  transition, including returns, Python exceptions, and VM faults.

`executes_iff_run` proves that `Executes` is equivalent to a halted runner result
at some finite fuel. `reaches_iff_run_exhausted` relates continuing paths to
exhausted runner results. Exhaustion is inconclusive; even a divergent loop has
a reachable continuation at every finite fuel bound. A halted frame cannot
resume through `Reaches`.

`Executes.deterministic` proves uniqueness of the entire terminal outcome and
frame. `run_halted_of_le` proves that increasing fuel preserves an observed halt.
Fuel still counts decoded instruction groups, as described in the
[bytecode guide](BYTECODE.md).

## Contract interface

`Verification/Contract.lean` defines `Contract Ghost` with three fields:

| Field | Meaning |
| --- | --- |
| `pre ghost initial` | Allowed initial frame and logical inputs |
| `post ghost initial value final` | Allowed normal result and final frame |
| `raises ghost initial exception final` | Allowed Python exception and failure frame |

Ghost inputs never become machine state. Both postconditions can refer to the
initial frame. Exception frames retain the existing instruction-entry snapshot
meaning, rather than modeling CPython stack unwinding.

`Contract.Accepts` dispatches to the appropriate postcondition and rejects every
VM fault, regardless of the user predicates. `PartialCorrect next contract`
requires every finite terminal execution from a pre-state to be accepted. This
allows divergence but excludes reachable faults: `reachable_no_fault` proves
that even an intermediate reachable frame cannot take a faulting next step.
Setting `raises` to `False` excludes Python exceptions as well.

`TotalCorrect` contains `partialCorrect` and `terminates`: every pre-state has a
finite terminal execution. `TotalCorrect.of_execution` and `of_run` construct it
from an allowed execution for **every** pre-state, using outcome determinism.
The fuel witness may depend on the input. This is a sequential rule; future
nondeterministic or asynchronous termination must quantify over schedules and
state any fairness assumptions.

These generic contracts do not automatically establish artifact metadata,
stack capacity, or a separate state invariant. The stack certificate provides
its own guarantees under the entry assumptions. Later invariant rules will
address additional reachable-state properties.

## Pre/post notation

Import `VeriPyAsm.Verification.Hoare` (also exported by `VeriPyAsm`) and enable
`open scoped VeriPyAsm.Verification.Hoare`:

```lean
import VeriPyAsm.Verification.Hoare

open VeriPyAsm.Semantics VeriPyAsm.Verification
open scoped VeriPyAsm.Verification.Hoare

-- P and Q are predicates over frames; S is the shallow program.
example (P Q : Frame → Prop) (S : Program) :
    {{ P }} S {{ Q }} → { P } S { Q } :=
  fun total => total.partialCorrect

-- Return binds an ordinary stack value; Q relates it to the stack after the pop.
example (value : Value) (rest : List Value) :
    {{ fun initial => initial.stack = value :: rest }}
      (fun _ => some Command.ret)
    {{ returns fun returned final => returned = value ∧ final.stack = rest }} := by
  apply TotalCorrect.of_run
  intro _ initial pre
  change initial.stack = value :: rest at pre
  refine ⟨1, .returned value { initial with stack := rest }, ?_, rfl, rfl⟩
  simp [run, step, Command.ret, pre]
```

The partial and total forms elaborate to Lean proof obligations. An explicit
`returns` marker makes the returned value available to the postcondition:

| Notation | Meaning |
| --- | --- |
| `{ P } S { Q }` | `PartialCorrect (step S) (Contract.ofFramePredicates P Q)` |
| `{{ P }} S {{ Q }}` | `TotalCorrect (step S) (Contract.ofFramePredicates P Q)` |
| `{ P } S { returns Q }` | `PartialCorrect (step S) (Contract.ofReturnPredicates P Q)` |
| `{{ P }} S {{ returns Q }}` | `TotalCorrect (step S) (Contract.ofReturnPredicates P Q)` |

`P` always has type `Frame → Prop`. Without `returns`, `Q` has type `Frame → Prop`;
with `returns`, it has type `Value → Frame → Prop`. Inspect `frame.stack` for
stack predicates or `frame.locals` and `frame.pc` for other state conditions. `S` has type
`Program`, so use `translation.program`, not `step translation.program` or a
single instruction command. Parenthesize program applications, for example
`(Embedding.compile code)`. Outer theorem binders such as `value` and `rest`
above remain available to both predicates.

All forms require normal return satisfying `Q` and reject Python exceptions and
VM faults. Partial correctness allows divergence; total correctness additionally
requires termination from every frame satisfying `P`. These are whole-program
judgments, not single-instruction or block rules. `Q` observes the actual final
frame: `RETURN_VALUE` has already popped the returned value. The `returns` form
passes that value separately to `Q`; it does not put it back on the stack. Use
the same `Value` operations and relations for the returned value and stack
elements: the marker names a value at a control-flow exit, not a different kind
of value. `Q` can relate it to any values in the final stack or locals, or to
logical inputs captured by the precondition. Use the full `Contract` interface
to relate initial and final states or permit an exception.
The [block judgments](RULES.md) express continuation postconditions for
non-return instructions, with separate fields for continuation, return, and
exception exits. The whole-program triples keep the meaning described above.

Both adapters use a `Unit` ghost, `pre := P`, and `raises := False`; their
postconditions observe the final frame or the returned value and final frame.
Expansion to each existing correctness predicate is checked
by `rfl`. The notation introduces a proposition for the user to prove; it does
not automatically prove the triple or run a VC generator.

## Imported `add1`

```lean
import VeriPyAsm.Examples.Add1

open VeriPyAsm VeriPyAsm.Semantics VeriPyAsm.Verification VeriPyAsm.Examples
open scoped VeriPyAsm.Verification.Hoare

#check add1Admitted.stack.valid
#check add1_total
#check add1_artifact_total
#check add1_no_exception
#check add1_no_fault

-- This is the statement proved directly by add1_total in Examples/Add1.lean.
example (n : Int) :
    {{ fun initial => initial = { locals := [some (.int n)] } }}
      add1Admitted.translation.program
    {{ returns fun value final =>
      value = .int (n + 1) ∧ final.locals = [some (.int n)] ∧ final.stack = [] }} :=
  add1_total n
```

`add1_total n` proves the result-aware total triple above. The retained
`add1Contract : Contract Int` specifies the same behavior relationally:

- Precondition: PC 0, empty stack, and exactly one local containing the integer `n`.
- Normal result: integer `n + 1`, unchanged locals, and an empty returned stack.
- Exceptional result: `False`.

The public contract mentions neither instruction offsets nor a fixed fuel budget.
`add1_total` composes the resume, load, push, binary-operation, and return rules,
checking their lookup in the certified shallow program. All inputs remain
symbolic. The separate `add1_run` lemma proves the five-instruction execution
fact by `rfl` for **every `n : Int`**. The total theorem uses the Hoare notation;
`add1_contract_total` derives the relational contract for artifact transport.
Its corollaries exclude exceptions and faults at every fuel bound. Boolean inputs are outside this
contract, though the modeled Python arithmetic also accepts them.

`Verification/Artifact.lean` defines `ArtifactPartialCorrect` and
`ArtifactTotalCorrect` through successful decoding and correctness of the decoded
reference program. Translation lemmas transport these judgments to and from the
shallow program using its checked representation equality; decoder functionality
prevents a different witness from choosing different code. The `add1` theorem
therefore concerns the original `add1Artifact`, with a separate stack-admission
certificate. These judgments do not authenticate extraction or prove refinement
of the CPython executable.

## Validation and next step

```sh
lake build VeriPyAsm ContractTests HoareTests BlockTests InstructionTests
```

The regressions distinguish partial from total correctness on a divergent loop,
reject immediate and delayed VM faults even with permissive postconditions,
exercise allowed Python exceptions, and test fuel/continuation boundaries. A
freshly admitted mutation of `add1` changes `LOAD_SMALL_INT 1` to `2`; a checked
counterexample refutes the original contract for that artifact. Proof-dependency
reports audit the execution rules, contract rules, and universal example.
Hoare tests additionally check exact expansion, parser precedence and ordinary
record syntax, captured inputs, the post-return stack, and rejection of an
incorrect returned-value postcondition.

Instruction/block composition and its semantic soundness are now implemented;
see the [rule guide](RULES.md) for the additional regression proofs. The next step
is invariant and ranking rules, followed by the manual total-correctness proof
for `triangular`. General VC generation,
exact-match proof registration, and Crush integration follow those proofs.
