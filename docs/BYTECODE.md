# First bytecode slice

This step implements the bytecode language, executable semantics, and translation
boundary from [the design](DESIGN.md). It does not implement contracts, VC generation,
proof registration, or solver integration.

## Use

External tools supply a closed Lean `CPython.V314.Artifact`: raw byte values,
scalar constants, code-object metadata, version/profile, and build provenance.
`bytecode% artifact` reduces the decoder during elaboration and returns an
`Embedding.Translation artifact` containing:

- `code`: decoded instructions with raw opcode/argument and byte offsets;
- `decoded`: `decode artifact = .ok code`, checked by definitional equality;
- `program`: a shallow Lean function mapping offsets to semantic commands;
- `correct`: `step program = referenceStep code`.

For example:

```lean
import VeriPyAsm.Examples.Bytecode

open VeriPyAsm VeriPyAsm.Semantics VeriPyAsm.Examples

def imported : Embedding.Translation add1Artifact := bytecode% add1Artifact

#check imported.decoded
#check imported.correct
#eval run (step imported.program) 5 { locals := [some (.int 41)] }
-- returns int 42, at byte offset 18
```

An unsupported literal causes an elaboration error with a byte offset and reason.
For data processed at runtime, `Embedding.translate` returns
`Except DecodeError (Translation artifact)` instead. There is no JSON/marshal
loader yet. The interface cannot represent constants outside int/bool/None;
external tools must reject those constants rather than coerce or omit them.

## Language and execution

The retained reference language is data. Its instructions denote native Lean
functions `Frame → StepResult`; translation builds the offset-to-command function.
There is one semantic command per decoded instruction. No block fusion or loop
restructuring is performed in this step. Both representations share the scalar
operations and command semantics.

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
| `BINARY_OP` | Add, subtract, multiply, and their scalar in-place variants |
| `COMPARE_OP` | Six comparisons, preserving/checking the full operand and its mask |
| `TO_BOOL` | Scalar truthiness |
| `POP_JUMP_IF_FALSE`, `POP_JUMP_IF_TRUE` | Forward offsets after caches; skip a following `NOT_TAKEN` on the untaken edge |
| `JUMP_FORWARD`, `JUMP_BACKWARD` | Absolute targets computed from cache-aware byte offsets |
| `RETURN_VALUE` | Pop and return the top value |

The decoder checks byte range, complete code units, zero baseline cache payloads,
operand indices, metadata, and every jump/fallthrough boundary. Cache payloads
never become executable instructions. Unsupported instructions are rejected even
when unreachable. `EXTENDED_ARG`, fused loads/stores, other arithmetic, handlers,
calls, heap objects, and asynchronous instructions remain unsupported.

**Successful decoding does not yet establish program safety.** Stack-height and
join consistency, `co_stacksize`, and definite initialization are not checked.
The current semantic stack is unbounded; underflow, invalid locals, and invalid
Boolean branches have explicit fault outcomes. These gaps must be addressed
before claiming an artifact is admitted for verification. The full prototype's
artifact schema/identity checks and loader also remain incomplete.

## Evidence and boundary

`Embedding.compile_correct` proves exact equality of the two step functions for
every decoded program and state, including failures. `compile_run` transports
that result to every fuel bound. No change in step count is hidden. These are
representation proofs relative to the defined semantics, not a refinement proof
of CPython's implementation or a proof of a function's intended contract.

```sh
lake build
lake build BytecodeTests
python3 tests/check_cpython.py
```

The Lean checks cover normal/exceptional execution, branch offsets, operand order,
malformed inputs, unsupported features, fuel exhaustion on a cycle, elaborator
rejection, and failure to reuse a certificate for changed bytes. The differential
harness checks 162 CPython outcomes across 19 artifacts and compares five stored
artifacts with actual code objects. It includes negative and large integers,
bool/int interactions, all implemented arithmetic/comparisons, both branch
directions, and unbound locals. These checks support conformance; they do not
prove runtime correspondence. Proof checking uses neither native evaluation
axioms nor external solver trust.

Instruction behavior was checked against the pinned
[CPython definitions](https://github.com/python/cpython/blob/v3.14.4/Python/bytecodes.c)
and [opcode IDs](https://github.com/python/cpython/blob/v3.14.4/Include/opcode_ids.h).
The next focused step is structural stack validation and the remaining encodings
needed by `triangular`, especially fused instructions and extended operands,
before starting specifications or VC generation.
