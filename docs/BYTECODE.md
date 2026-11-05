# Bytecode and stack admission

The implemented slice covers the bytecode language, executable semantics,
translation, and stack admission from [the design](DESIGN.md). The separate
[contract interface](CONTRACTS.md) adds partial/total correctness and a universal
imported `add1` proof. VC generation, proof registration, and solver integration
remain later milestones.

## Use

External tools supply a closed Lean `CPython.V314.Artifact`: raw byte values,
scalar constants, code-object metadata, version/profile, and build provenance.
`bytecode% artifact` reduces the decoder during elaboration and returns an
`Embedding.Translation artifact` containing:

- `code`: decoded instruction groups with terminal opcode, full operand, and byte offsets;
- `decoded`: `decode artifact = .ok code`, checked by definitional equality;
- `program`: a shallow Lean function mapping offsets to semantic commands;
- `correct`: `step program = referenceStep code`.

`admit_bytecode% artifact` returns `StackAdmitted artifact`, containing that
`translation` and a `stack` certificate indexed by exactly `translation.code`
and `artifact.stackSize`. Translation alone does not check stack admission.

For example:

```lean
import VeriPyAsm.Examples.Bytecode

open VeriPyAsm VeriPyAsm.Semantics VeriPyAsm.Examples

def imported : Embedding.Translation add1Artifact := bytecode% add1Artifact
def admitted : StackAdmitted add1Artifact := admit_bytecode% add1Artifact

#check imported.decoded
#check imported.correct
#check admitted.stack.valid
#check StackAdmitted.run_no_underflow
#eval run (step imported.program) 5 { locals := [some (.int 41)] }
-- returns int 42, at byte offset 18
```

An unsupported literal causes an elaboration error with a byte offset and reason.
For data processed at runtime, `Embedding.translate` returns
`Except DecodeError (Translation artifact)`, while `admit` returns
`Except AdmissionError (StackAdmitted artifact)`. Admission errors distinguish
decoding failures from stack-analysis failures. There is no JSON/marshal loader
yet. The interface cannot represent constants outside int/bool/None; external
tools must reject those constants rather than coerce or omit them.

## Stack certificate boundary

The implementation separates four responsibilities:

| Module under `CPython/V314/Stack/` | Responsibility |
| --- | --- |
| `Rules.lean` | Required operands, produced values, and the exact one-value return rule |
| `Certificate.lean` | Finite height table and the independently decidable `Valid` proposition |
| `Analyze.lean` | Worklist that proposes heights and reports inconsistent edges or capacity errors |
| `Soundness.lean` | Proofs relating those rules and certificates to instruction and execution semantics |

`Valid` requires entry PC 0 at height 0, unique table offsets, a valid instruction
at every listed offset, enough operands, input/output heights within capacity,
and matching heights at every normal successor. Both conditional edges are
checked even when a condition is constant. These local checks close the table
under control flow, including cycles. The worklist's traversal and fuel bound
are not trusted: admission requires the separate certificate proof.

Only instructions reachable through normal control-flow edges need stack-table
entries. Dead instructions still undergo the decoder's global encoding checks.
Python exception paths terminate in this handler-free fragment, so an operation
that can raise TypeError or UnboundLocalError remains admissible when its normal
path has a valid shape.

## Language and execution

The retained reference language is data. Its instructions denote native Lean
functions `Frame → StepResult`; translation builds the offset-to-command function.
There is one semantic command per decoded instruction group: any `EXTENDED_ARG`
prefixes, the terminal opcode, and its caches. Compiler-emitted fused local
instructions execute atomically in this model; no additional block fusion or
loop restructuring is performed. Both representations share the scalar operations
and command semantics. Fuel counts these groups, not CPython's internal dispatches.

Frames explicitly retain PC, optional local values, and operand stack. The stack
head is the top. Outcomes distinguish continuation, return, Python exception,
and VM fault. Exception/fault frames are snapshots at instruction entry, not an
attempt to model CPython stack unwinding. Fuel exhaustion retains a continuation
and is inconclusive. Loops are PC transitions, not recursive Lean functions whose
termination must be proved merely to represent the program.

Values are exact built-in integers, booleans, and None. Arithmetic coerces bools
to 0/1 and returns integers. Equality respects bool/int equality; ordered
comparisons with None raise TypeError. Unbound `LOAD_FAST_CHECK` raises
UnboundLocalError; an unbound unchecked load is a VM fault. Conditional jumps
require bool; `TO_BOOL` performs truth conversion separately.

## Admitted encoding

Only CPython 3.14.4 baseline code under the documented sequential profile is
accepted. Functions must have flags 3, no keyword-only arguments, names/globals,
closure slots, or exception table. Metadata/profile declarations are assumptions
about extraction and execution, not authenticated evidence.

| Instructions | Scope |
| --- | --- |
| `RESUME`, `NOT_TAKEN` | Entry `RESUME 0`; no instrumentation or asynchronous runtime events |
| `LOAD_CONST`, `LOAD_SMALL_INT` | Scalar constants; one-byte small integer operand |
| `LOAD_FAST`, `LOAD_FAST_BORROW`, `LOAD_FAST_CHECK`, `STORE_FAST` | Checked local indices; borrowing unobservable in this scalar profile |
| `LOAD_FAST_LOAD_FAST`, `LOAD_FAST_BORROW_LOAD_FAST_BORROW` | Two locals packed into high/low nibbles; second value ends up on top |
| `STORE_FAST_LOAD_FAST`, `STORE_FAST_STORE_FAST` | Packed local indices; store before reload, or store the top value first; aliases preserve assignment order |
| `BINARY_OP` | Add, subtract, multiply, and their scalar in-place variants |
| `COMPARE_OP` | Six comparisons, preserving/checking the full operand and its mask |
| `TO_BOOL` | Scalar truthiness |
| `POP_JUMP_IF_FALSE`, `POP_JUMP_IF_TRUE` | Forward offsets after caches; skip a following `NOT_TAKEN` on the untaken edge |
| `JUMP_FORWARD`, `JUMP_BACKWARD` | Absolute targets computed from cache-aware byte offsets |
| `RETURN_VALUE` | Pop and return the top value |

`Wordcode.lean` parses up to three `EXTENDED_ARG` prefixes independently of
opcode interpretation. The first prefix must be nonzero; the combined operand
must fit a nonnegative signed 32-bit integer. Opcode-specific bounds still apply:
packed fused operands and `LOAD_SMALL_INT` remain one byte. The instruction's
`offset` is the group start and `next` is after the terminal opcode's caches.
Jumps may target a group start, never an interior prefix, terminal opcode inside
a prefixed group, or cache word. Original bytes remain in the artifact.

The decoder checks byte range, complete code units, zero baseline cache payloads,
operand indices, metadata, and every jump/fallthrough boundary. Cache payloads
never become executable instructions. Unsupported instructions are rejected even
when unreachable. Other arithmetic, handlers, calls, heap objects, and asynchronous
instructions remain unsupported.

**Stack admission does not establish complete program safety.** It checks heights,
joins, return shape, and `co_stacksize`; it does not establish value tags or local
initialization. Invalid-local, unchecked-unbound-local, and non-Boolean-branch
faults remain explicit possibilities. Python exceptions are allowed, and no
termination or functional contract is claimed. The model uses an unbounded list
for the stack; the certificate proves that admitted executions from entry stay
within the declared capacity. Artifact identity checks and the full loader also
remain incomplete.

## Evidence and boundary

`Embedding.compile_correct` proves exact equality of the two step functions for
every decoded program and state, including failures. `compile_run` transports
that result to every fuel bound, counting the same instruction groups. These are
representation proofs relative to the defined semantics, not a refinement proof
of CPython's implementation or a proof of a function's intended contract.

The stack soundness proofs establish instruction and continuation-height
preservation, absence of stack underflow, and an empty operand stack after return.
`StackAdmitted.run_no_underflow`, `run_exhausted_bound`, and `run_return_stack`
transport these properties to the shallow program for every fuel bound from an
entry frame with an empty stack. The guarantees allow both divergence and Python
exceptions; they do not depend on a particular worklist result or test input.
The four fused local instructions have no intermediate stack peak above their
input/output heights, so the existing capacity criterion suffices for them.

`Examples/Triangular.lean` now contains the real compiled loop, its stack
certificate, and a universal no-underflow theorem. Its arithmetic and termination
contract is still unproved. Bounded executions are regression examples only.

```sh
lake build VeriPyAsm BytecodeTests StackCertificateTests StackTests AdmissionTests
lake build FusedSemanticsTests WordcodeTests ExtendedDecodeTests FusedDecodeTests
python3 tests/check_cpython.py
```

The Lean checks cover normal/exceptional execution, branch offsets, operand order,
malformed inputs, unsupported features, fuel exhaustion on a cycle, elaborator
rejection, and failure to reuse a certificate for changed bytes or capacity.
Stack checks also cover missing/tampered certificate entries, inconsistent joins
and backedges, operand requirements distinct from net effects, excess values at
return, capacity violations, and valid infinite loops. The differential harness
checks 189 CPython outcomes, stack-admits all 27 artifacts, and compares six stored
artifacts with actual code objects. It includes negative and large integers,
bool/int interactions, all implemented arithmetic/comparisons, both branch
directions, unbound locals, all four fused instructions, and extended constant,
local, and jump operands. Decoded group spans and operands are compared with
CPython's `dis` output. Large fixtures use explicit finite local elaboration
budgets; small fixtures retain Lean's defaults. The largest artifact has 517
instructions, and the full harness can take several minutes to kernel-check.
These checks support conformance;
they do not prove runtime correspondence. Proof checking uses neither native
evaluation axioms nor external solver trust.

The elaborators use Lean's kernel reducer to inspect closed decoding and analysis
results. The returned translation and independent stack-validity proof are still
checked by the kernel; this does not execute compiled native code as proof evidence.

Instruction behavior was checked against the pinned
[CPython definitions](https://github.com/python/cpython/blob/v3.14.4/Python/bytecodes.c)
and [opcode IDs](https://github.com/python/cpython/blob/v3.14.4/Include/opcode_ids.h).
Prefix and span handling was also checked against
[`dis`](https://github.com/python/cpython/blob/v3.14.4/Lib/dis.py) and the
[assembler](https://github.com/python/cpython/blob/v3.14.4/Python/assemble.c).
The contract/execution interface and universal `add1` and `triangular` proofs are
described in the [contract guide](CONTRACTS.md). Sound instruction/block/loop rules
support those proofs; general VC generation remains future work.
Any later instruction must extend the stack rules and their semantic proof,
including intermediate peak height when needed.
