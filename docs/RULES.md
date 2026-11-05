# Instruction and block proof rules

Import `VeriPyAsm.Verification.Instruction` (also exported by `VeriPyAsm`).
The rules compose proofs about shallow commands and the actual program's
instruction lookup. They are proved against the existing deterministic machine;
there is no additional executable language or solver dependency.

## Exit postconditions

`Postcondition` distinguishes three observations:

| Field | Type | Observation |
| --- | --- | --- |
| `continues` | `Frame → Prop` | Frame at a designated continuation location |
| `returned` | `Value → Frame → Prop` | Ordinary returned value and frame after popping it |
| `raises` | `PythonException → Frame → Prop` | Python exception and instruction-entry snapshot |

Each field defaults to `False`. `Postcondition.Accepts` always rejects VM faults.
Both the returned value and stack elements have type `Value`; a predicate can
relate them directly. The field is named `returned` so record construction works
alongside the scoped Hoare notation's `returns` marker.

Predicates are native Lean propositions. Outer binders can capture ghost inputs,
initial frames, or any other logical parameters. These rules do not establish
stack capacity or artifact metadata; those remain admission properties.

## Block boundaries and soundness

`BlockExecutes next exits initial result`, in `Semantics/Block.lean`, stops at the
**first** location satisfying `exits : Nat → Prop`, before executing that
instruction. It otherwise takes ordinary machine steps until an exit or halt:

- `.next final`: a continuation at a designated exit, including zero steps when
  the initial location is already an exit.
- `.halted outcome`: a normal return, Python exception, or VM fault.

`BlockExecutes.sound` connects these cases to `Reaches` and `Executes`, and proves
that every continuation ends at an exit. `deterministic` proves uniqueness of the
block outcome. An exit may have no instruction: continuing from it requires a
separate proof. A return or exception cannot resume as a continuation.

`Verification/Block.lean` defines:

```text
BlockPartialCorrect next exits P Q
  Every finite block execution from P satisfies Q.

BlockTotalCorrect next exits P Q
  Partial correctness, plus a finite block execution from every P-state.
```

Partial correctness allows divergence but forbids faults before an exit. Total
block correctness guarantees reaching an allowed boundary or halt; the program
may continue after that boundary. With `exits := fun _ => False`, the methods
`to_partialCorrect` and `to_totalCorrect` establish the existing whole-program
contracts. Their normal-return instances expand to the existing Hoare triples.
These termination rules rely on sequential determinism; future scheduler rules
must handle all permitted schedules separately.

## Composition rules

| Rule | Purpose |
| --- | --- |
| `BlockTotalCorrect.exit` | Establish a zero-step continuation at an exit |
| `BlockPartialCorrect.consequence`, `BlockTotalCorrect.consequence` | Strengthen the precondition and weaken accepted postconditions |
| `BlockPartialCorrect.seq`, `BlockTotalCorrect.seq` | Compose through an intermediate continuation assertion |
| `InstructionCorrect.consequence`, `cases` | Adapt a one-step rule or combine alternative preconditions |
| `InstructionCorrect.on_frame` | Specialize a rule to an explicitly given symbolic frame |
| `InstructionCorrect.prepend_partial`, `prepend` | Prepend an instruction to a partial or total block proof |
| `InstructionCorrect.to_block` | Lift one instruction into a total block proof |

For sequencing, the prefix uses `{ Q with continues := R }` and the suffix uses
precondition `R` and postcondition `Q`. Thus only continuing exits invoke the
suffix; early returns and exceptions already satisfy the final postcondition.
Every final exit must be included in the prefix's cutpoints. This prevents
executing past an earlier final exit; typically use the union of intermediate
locations and final exits.

```lean
import VeriPyAsm.Verification.Instruction

open VeriPyAsm.Semantics VeriPyAsm.Verification

example (next : Frame → StepResult) (cuts exits : Nat → Prop)
    (P R : Frame → Prop) (Q : Postcondition)
    (first : BlockTotalCorrect next cuts P { Q with continues := R })
    (second : BlockTotalCorrect next exits R Q)
    (contains : ∀ pc, exits pc → cuts pc) :
    BlockTotalCorrect next exits P Q :=
  first.seq second contains
```

`prepend` and `prepend_partial` require proof of the actual command lookup for
every pre-state and that the current PC is outside the block's exit set.
`to_block` additionally requires that every permitted continuation is an exit.
These premises ensure instruction rules describe the imported program and
respect the observation boundary.

## Instruction rules

`InstructionCorrect command P Q` means `∀ s, P s → Q.Accepts (command s)`.
The following theorems expose sufficient preconditions for each scalar command:

| Rule | Required facts |
| --- | --- |
| `jump`, `push` | Continuation postcondition holds on the updated frame |
| `load` | Indexed local exists and contains the loaded value |
| `loadPair` (import `Verification.FusedInstruction`) | Both indexed locals are initialized; the second loaded value is on top |
| `load_unbound` | Checked load finds an unbound local and `raises` permits it |
| `store` | Local index is in bounds, stack has a top value, updated frame satisfies `continues` |
| `binary` | Stack is `right :: left :: rest`, operation returns `.ok value`, updated frame satisfies `continues` |
| `binary_error` | Same operand order, operation returns `.error exception`, original frame satisfies `raises` |
| `toBool` | Stack is nonempty; replacing its top by its truthiness satisfies `continues` |
| `branch` | Stack top is an exact bool; the selected destination and remaining stack satisfy `continues` |
| `ret` | Stack is `value :: rest`; `returned value` holds on the frame with stack `rest` |

Arithmetic and comparisons share `binary`, whose operation remains an explicit
argument. Rules preserve the rest of the frame through record updates. The
conditions are ordinary Lean goals available to later VC generation and Crush.
The present interface also accepts a directly proved `InstructionCorrect` for
any shallow command. The atomic pair-of-loads rule supports the first loop proof;
dedicated rules for fused stores can be added as needed.

Here is a non-returning instruction with a stack postcondition:

```lean
import VeriPyAsm.Verification.Instruction

open VeriPyAsm.Semantics VeriPyAsm.Verification

example (value : Value) (rest : List Value) :
    BlockTotalCorrect (step (fun _ => some (Command.push 1 value))) (fun pc => pc = 1)
      (fun s => s = { stack := rest })
      { continues := fun s => s.pc = 1 ∧ s.stack = value :: rest } := by
  have rule := (InstructionCorrect.push 1 value
    { continues := fun s => s.pc = 1 ∧ s.stack = value :: rest }).on_frame
    (initial := { stack := rest }) ⟨rfl, rfl⟩
  exact rule.to_block (fun _ _ => rfl)
    (by rintro s rfl; simp) (fun _ post => post.1)
```

The whole-program Hoare notation retains its meaning. Use the block judgments
above for continuation postconditions and the `returns` form for properties
involving a returned value. `Examples/Add1.lean` now derives its universal total
triple from instruction rules, program-lookup proofs, and block composition.
Its artifact theorem still follows from the translation's checked correspondence.

## Loop invariants and ranking

Import `VeriPyAsm.Verification.Loop` (also exported by `VeriPyAsm`). An
`IterationExecutes` path must execute at least one instruction before observing
its next cutpoint. It may return or raise first. `IterationPartialCorrect` and
`IterationTotalCorrect` specify such paths. The rules
`InstructionCorrect.start_iteration_partial` and `start_iteration` compose the
first instruction with an ordinary block proof, checking program lookup.

`BlockPartialCorrect.loop` requires an invariant `I` and a partially correct
iteration: every continuing result either reaches a final exit satisfying
`Q.continues`, or reestablishes `I`. Terminal results satisfy `Q` directly.
Divergence is allowed; faults are forbidden. Its soundness proof inducts over
finite execution progress, not over an assumed termination rank.

`BlockTotalCorrect.loop` additionally requires total correctness of each
iteration and a `rank : Frame → Nat` that **strictly decreases** whenever an
iteration reestablishes `I`. Only comparisons between invariant states need a
decrease. `loop_wellFounded` accepts any well-founded relation, oriented
`decreases new old`, for lexicographic and other rankings.

Both rules require every final exit to be among the iteration cutpoints and
every invariant state to be outside the final exits. An entry prefix establishes
`I`; the loop yields a block contract that can be sequenced with an exit suffix.
Multiple header locations are possible when `I` covers each one. Local cycle
coverage is a proof obligation: a total iteration must reach its next cutpoint
or halt. A decreasing header rank does not discharge an inner divergent path.

The [triangular proof](CONTRACTS.md#imported-triangular) applies these rules to the
imported bytes with cutpoints 6 and 58, the mathematical sum invariant, and rank
`n.toNat`. Its separate entry and return blocks assemble the full contract.

## Validation

```sh
lake build VeriPyAsm BlockTests InstructionTests LoopTests ContractTests HoareTests
lake build TriangularTests
```

The regressions cover first-exit behavior, early return/exception propagation,
partial versus total correctness on divergence, store/reload composition,
noncommutative operand order, both branch edges, and failures from invalid local
access, unchecked unbound loads, non-boolean branches, and empty returns.
The examples also relate the returned value to locals and a remaining stack.
Loop regressions reject zero-step iterations, unchanged ranks, and divergent
bodies in total mode, while permitting divergent invariant-preserving loops in
partial mode and allowed early returns or exceptions in either mode.
Dependency reports contain only standard Lean axioms, with no `sorryAx`, native
decision axiom, project-specific axiom, or solver-trust dependency.
