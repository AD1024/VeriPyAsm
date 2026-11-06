# Supported profile and trust boundary

Profile revision **1**, CPython **3.14.4**, Lean **4.34.0**. This document describes
the implemented prototype. Instruction or assumption changes should update it
alongside their code and regression tests.

## Artifact and runtime profile

The [artifact interface](VeriPyAsm/CPython/V314/Artifact.lean) accepts Lean literals
for baseline bytecode and code-object metadata. It is not a `.pyc` or marshal
loader. The [decoder](VeriPyAsm/CPython/V314/Decode.lean) requires:

- Artifact schema 1, implementation `cpython`, version `3.14.4`, a nonempty build
  identity, profile `baselineSequential`, and `optimize = 0`.
- Ordinary function flags `3`, consistent positional argument/local counts, no
  keyword-only arguments, globals/names, closure slots, or exception handlers.
- Scalar constants, complete two-byte code units, valid operands and control-flow
  targets, and zero baseline cache payloads. Unsupported instructions are rejected
  even when unreachable.

The intended runtime is single-threaded, without tracing, instrumentation, JIT,
signals, or resource exhaustion. Recorded version/build/profile declarations are
not authenticated evidence of the actual interpreter or runtime configuration.
Specialized/adaptive instruction streams are outside the accepted input profile.

| Instruction family | Supported scope |
| --- | --- |
| `RESUME`, `NOT_TAKEN` | Entry `RESUME 0`; ordinary sequential control flow |
| `LOAD_CONST`, `LOAD_SMALL_INT` | Integers, booleans, `None`; small integer operands fit one byte |
| `LOAD_FAST`, `LOAD_FAST_BORROW`, `LOAD_FAST_CHECK`, `STORE_FAST` | Indexed local slots with separate ownership admission |
| `LOAD_FAST_LOAD_FAST`, `LOAD_FAST_BORROW_LOAD_FAST_BORROW`, `STORE_FAST_LOAD_FAST`, `STORE_FAST_STORE_FAST` | Two local indices packed into one operand; ordered fused effects |
| `BINARY_OP` | Addition, subtraction, multiplication, including scalar in-place variants |
| `COMPARE_OP`, `TO_BOOL` | Six comparisons and scalar truth conversion |
| `POP_JUMP_IF_FALSE`, `POP_JUMP_IF_TRUE`, `JUMP_FORWARD`, `JUMP_BACKWARD` | Checked instruction-group targets and cache-aware offsets |
| `RETURN_VALUE` | Pop the returned value; admitted returns leave an empty stack |
| `LOAD_COMMON_CONSTANT 0`, `RAISE_VARARGS 1` | An immediate AssertionError load/raise pair, with no incoming edge bypassing the load |
| `EXTENDED_ARG` | Up to three prefixes; a nonzero first prefix, a nonnegative signed 32-bit combined operand, and instruction-specific bounds |

The [value model](VeriPyAsm/Semantics/Value.lean) represents mathematical integers,
booleans, and `None`. Booleans participate in native scalar arithmetic as 0/1 while
retaining a distinct tag. Intended inputs are exact built-in scalar types, without
subclasses or overloaded operations; a native contract must constrain its input
tags. Admission and `EntryFrame` alone do not establish those tags.

An internal value denotes the AssertionError class. It cannot be an artifact
constant; decoding restricts its loading to the failure pair above. Assertions
execute their tests and can raise; they never introduce assumed facts. Messages,
constructors, other raises/common constants, and `NOP`-folded assertions are
unsupported. General objects, calls, mutation, handlers, generators, and async
execution remain future extensions.

## What a verified result establishes

The public [VerifiedArtifact](VeriPyAsm/Verification/VerifiedArtifact.lean) combines:

1. Successful decoding and a representation theorem equating shallow execution
   with decoded reference execution for the same artifact.
2. Stack and ownership certificates. Stack checks cover heights, joins, capacity,
   and return shape. Ownership checks track local-backed borrows, reject stores of
   borrowed values and owner overwrites while a borrow is live, and account for
   fused operations. They model a reference protocol, not CPython's allocator.
3. A proof that every contract pre-state starts at PC zero with an empty stack,
   initialized argument slots, and unbound remaining locals.
4. Partial or total correctness under the explicit Lean semantics.

Partial correctness constrains every finite terminal execution and excludes VM
faults; it permits divergence. Total correctness additionally proves termination
from every pre-state. Both enforce normal and exceptional postconditions. A
satisfiable precondition is not required automatically: users should inspect it
when judging whether a contract expresses their intended inputs.

Exceptions are modeled as TypeError, UnboundLocalError, or AssertionError with an
instruction-entry frame snapshot. Actual exception unwinding and resource failures
are not modeled. Bounded execution is useful for tests but is not a termination
proof. Lower-level `ArtifactPartialCorrect` and `ArtifactTotalCorrect` deliberately
omit admission and are not final verification packages.

## Proof production and assurance

[VC generation](VeriPyAsm/Verification/VC/Generate.lean) produces closed Lean
propositions, kernel-checked normalization equalities, and a conditional assembly
theorem. Graph traversal and simplification choose obligations but cannot certify
correctness without their proofs. Scoped loops use local invariant/ranking rules;
their obligations are currently grouped into `VC.entry` and `VC.execution`.

Manual `@[veripy_proof VC.name]` registration checks the complete theorem type
against the named VC using a kernel-checked equality by `rfl`. Registration and
discharge audit transitive dependencies, including the theorem statement.

| Policy | Permitted axioms beyond Lean's kernel rules |
| --- | --- |
| `checked` (default) | `propext`, `Classical.choice`, `Quot.sound` |
| `solver_trusted` (explicit) | The checked set plus `Crush.crushSorry` |

Neither policy permits `sorryAx` or native-decision trust. Reports derive assurance
from actual dependencies and identify the proof provider and observed backend.
The Crush adapter does not silently switch to solver trust. An incomplete strict
`veripy_verify` run exports no package; VC generation or discovery alone is not
successful verification. `make check-crush` builds regressions, runs transitive
axiom audits, compares executions with CPython, and checks the source frontend.

## Source frontend and remaining boundary

The Python frontend compiles source bytes without executing the module, using
`dont_inherit=True` and `optimize=0`. It selects one ordinary top-level function
with positional integer parameters, assignments, `if`, at least one `while`, and
a final integer return. Annotations support integer arithmetic/comparisons,
logical connectives, `is_int`, `old(parameter)`, and `result` in postconditions.
Decorators, defaults, varargs, and keyword-only parameters are rejected. This
source grammar remains subject to bytecode admission and CFG mapping checks;
unsupported compiler output is rejected rather than approximated.

Function blocks accept `requires`, `ensures`, and optional `mode`; loop blocks
accept `loop`, `invariant`, and `decreases`. Repeated predicates are conjoined.
Total mode is the default and requires a measure per loop; partial mode rejects
measures. Type guards, postconditions, and loop invariants must be explicit when
generating VCs. Source contracts currently forbid all exceptions. Source `assert`
checkpoints, ghost hints, `for`, `break`, and `continue` are not yet supported.

Directive attachment follows [Python physical lines](https://docs.python.org/3.14/reference/lexical_analysis.html#physical-lines)
(LF, CRLF, or CR), with
token-based statement boundaries and matching indentation. Ordinary comments and
blank lines may intervene. Every directive in the selected function's header/body
must be consumed or rejected. Raw source bytes and compiled metadata remain in
the companion bundle.

Companion bundle schema **2** adds `directives`: an ordered inventory for the
selected function, preserving each parsed kind/expression, original comment text,
source span, and attachment target (function name or loop label and statement
span). Lines are one-based; columns are zero-based UTF-8 byte offsets, with
exclusive ends, matching Python AST/source-map coordinates. Repeated clauses
remain separate entries. The nested artifact and source-map input schemas remain
at version 1. The inventory supports review; it is not additional Lean proof
evidence for source extraction.

Checked source/CFG mappings establish structural properties such as boundaries,
edges, domination, nesting, and cycle coverage. They do not authenticate source
positions or prove the Python parser faithfully extracted the intended
annotations. The representation theorem similarly shares instruction semantics
with the reference dispatcher; it is not a refinement proof of the CPython C
implementation. Runtime correspondence and source/specification fidelity remain
external obligations. Differential tests supply evidence, not universal proofs.

Next steps include source proof checkpoints, separate named obligations for each
scoped loop, and marker-confinement lemmas toward runtime refinement. These are
extensions to the present guarantee, not premises supplied by the current tests.
