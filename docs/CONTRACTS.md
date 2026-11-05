# Sequential contracts and the first program proof

The current contract interface uses native Lean predicates. It supports partial
and total correctness for the deterministic scalar machine, including normal and
exceptional exits. It does not yet provide a specification parser, loop rules,
generated VCs, proof registration, or solver discharge.

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

## Imported `add1`

```lean
import VeriPyAsm.Examples.Add1

open VeriPyAsm VeriPyAsm.Semantics VeriPyAsm.Verification VeriPyAsm.Examples

#check add1Admitted.stack.valid
#check add1_total
#check add1_artifact_total
#check add1_no_exception
#check add1_no_fault
```

`add1Contract : Contract Int` specifies:

- Precondition: PC 0, empty stack, and exactly one local containing the integer `n`.
- Normal result: integer `n + 1`, unchanged locals, and an empty returned stack.
- Exceptional result: `False`.

The public contract mentions neither instruction offsets nor a fixed fuel budget.
The supporting `add1_run` lemma proves symbolically, by `rfl`, that the certified
shallow program returns the specified result in five instructions for **every
`n : Int`**. `add1_total` assembles total correctness, and its corollaries exclude
exceptions and faults at every fuel bound. Boolean inputs are outside this
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
lake build VeriPyAsm ContractTests
```

The regressions distinguish partial from total correctness on a divergent loop,
reject immediate and delayed VM faults even with permissive postconditions,
exercise allowed Python exceptions, and test fuel/continuation boundaries. A
freshly admitted mutation of `add1` changes `LOAD_SMALL_INT 1` to `2`; a checked
counterexample refutes the original contract for that artifact. Proof-dependency
reports audit the execution rules, contract rules, and universal example.

The next step is reusable instruction/block and invariant rules, followed by the
manual invariant and termination proof for `triangular`. General VC generation,
exact-match proof registration, and Crush integration follow those proofs.
