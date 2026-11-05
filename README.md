# VeriPyAsm

VeriPyAsm will verify Python programs by proving properties of their compiled
CPython bytecode in Lean 4. The long-term target includes mutable objects,
exceptions, library calls, and asynchronous programs.

**Status:** scalar bytecode, stack admission, and sequential contracts are implemented.
`bytecode% artifact` decodes CPython 3.14.4 baseline bytes and produces a certified
translation into shallow Lean commands. `admit_bytecode% artifact` also checks
stack requirements, consistent heights across control flow, exact return shape,
and the artifact's declared stack capacity. The resulting certificate supports
kernel-checked stack-safety theorems. See the [bytecode guide](docs/BYTECODE.md)
for the precise guarantees and remaining limits. Fused local instructions and
extended operands are supported. The compiled `triangular` loop has a stack
certificate; its functional and termination contract is not yet verified.

The [contract interface](docs/CONTRACTS.md) now has a universal total-correctness
proof for the imported `add1` artifact: every integer input returns its successor,
preserves its local, and terminates without Python exceptions or VM faults.
Scoped `{ P } S { Q }` and `{{ P }} S {{ Q }}` notation expresses partial and
total correctness with frame predicates, including operand-stack conditions.
The explicit `returns Q` postcondition also observes the returned value;
`Examples/Add1.lean` uses this form for its successor guarantee.
The [instruction and block rules](docs/RULES.md) now derive that proof by
composition, with explicit continuation, return, and exception postconditions.

The [verification-flow design](docs/DESIGN.md) specifies shallow elaboration,
contracts, VC generation, configurable Crush discharge, proof reporting, and the
manual `@[veripy_proof ...]` handoff. A full specification DSL, VC generation, and proof
registration remain planned. Stack admission establishes structural properties;
functional correctness and exception freedom require separate contract proofs.

The [prototype plan](docs/PROTOTYPE.md) specifies the first Python fragment,
normal and exceptional contracts, termination obligations, artifact provenance,
validation strategy, and the staged route to async verification.

The [Crush integration assessment](docs/CRUSH.md) proposes checked automation for
verification conditions and records a small successful proof experiment.

## Build

The project pins **Lean 4.34.0** and a reviewed Crush revision through Lake.
With that toolchain installed through Elan, build the core library with:

```sh
lake build
```

Check bytecode examples, admission/rejection cases, and proof dependencies with:

```sh
lake build BytecodeTests StackCertificateTests StackTests AdmissionTests
lake build FusedSemanticsTests WordcodeTests ExtendedDecodeTests FusedDecodeTests
lake build ContractTests HoareTests BlockTests InstructionTests
python3 tests/check_cpython.py  # requires CPython 3.14.4
```

The Python check compares real code objects and normal/exceptional outcomes with
the Lean model and checks stack admission for the corpus. It is a test oracle,
not a production source-to-bytecode tool.

To check the five Crush proof examples, with cvc5 1.3.4 or a compatible version
on `PATH`:

```sh
lake build CrushObligations
```

Open this project directory in VS Code. Lake supplies Crush's import paths to the
Lean extension; no custom `LEAN_PATH` is needed. After a dependency configuration
change, use **Lean 4: Restart File** if an open file retains an old import error.

The intended interpreter is **CPython 3.14.4**, also recorded in
`.python-version` and `VeriPyAsm/Target.lean`. Python is not required to build the
Lean library. The decoder and conformance test check the implementation and exact
release. External tools supply artifacts; there is no production extractor yet.

## Current files

| Path | Purpose |
| --- | --- |
| `VeriPyAsm.lean` | Library entry point |
| `VeriPyAsm/Target.lean` | Intended interpreter metadata |
| `VeriPyAsm/Semantics/` | Scalars, frames, commands, finite execution relations, and bounded runner |
| `VeriPyAsm/CPython/V314/` | Artifact data, reference language, conservative decoder |
| `VeriPyAsm/CPython/V314/Stack/` | Stack rules, certificate checker, analysis, soundness proofs |
| `VeriPyAsm/Embedding.lean` | Shallow translation and correspondence proofs |
| `VeriPyAsm/Admission.lean` | Stack admission bound to the exact artifact and capacity |
| `VeriPyAsm/Bytecode.lean` | `bytecode%` and `admit_bytecode%` term elaborators |
| `VeriPyAsm/Verification/` | Contracts, instruction/block rules, partial/total correctness, artifact transport |
| `VeriPyAsm/Examples/Bytecode.lean` | Five literal artifacts and certified embeddings |
| `VeriPyAsm/Examples/Add1.lean` | Universal total-correctness proof for imported integer `add1` |
| `VeriPyAsm/Examples/Triangular.lean` | Imported loop, stack certificate, and no-underflow theorem |
| `tests/` | Kernel-checked regression cases and CPython conformance checks |
| `docs/BYTECODE.md` | Implemented slice, usage, and limitations |
| `docs/CONTRACTS.md` | Contract interface, execution rules, first program proof |
| `docs/RULES.md` | Sound instruction/block rules, continuation boundaries, compositional proofs |
| `docs/DESIGN.md` | Verification flow and proposed user interface |
| `docs/PROTOTYPE.md` | Design and implementation milestones |
| `docs/CRUSH.md` | Automation design, trust policy, and experiment results |
| `examples/python/triangular.py` | First planned program proof |
| `experiments/CrushObligations.lean` | Checked VC experiment, built with `lake build CrushObligations` |

The guarantees are relative to the explicit Lean operational semantics.
Correspondence with the actual CPython runtime is a separate
obligation, supported initially by source inspection and differential testing.
