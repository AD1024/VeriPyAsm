# VeriPyAsm

VeriPyAsm will verify Python programs by proving properties of their compiled
CPython bytecode in Lean 4. The long-term target includes mutable objects,
exceptions, library calls, and asynchronous programs.

**Status:** the scalar bytecode slice and stack admission are implemented.
`bytecode% artifact` decodes CPython 3.14.4 baseline bytes and produces a certified
translation into shallow Lean commands. `admit_bytecode% artifact` also checks
stack requirements, consistent heights across control flow, exact return shape,
and the artifact's declared stack capacity. The resulting certificate supports
kernel-checked stack-safety theorems. See the [bytecode guide](docs/BYTECODE.md)
for the precise guarantees and remaining limits. The `triangular` contract is
not yet verified.

The [verification-flow design](docs/DESIGN.md) specifies shallow elaboration,
contracts, VC generation, configurable Crush discharge, proof reporting, and the
manual `@[veripy_proof ...]` handoff. Contracts, VC generation, and proof
registration remain planned. Stack admission establishes structural properties;
type/local-initialization safety and program contracts remain separate work.

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
| `VeriPyAsm/Semantics/` | Scalars, frames, outcomes, semantic commands, bounded execution |
| `VeriPyAsm/CPython/V314/` | Artifact data, reference language, conservative decoder |
| `VeriPyAsm/CPython/V314/Stack/` | Stack rules, certificate checker, analysis, soundness proofs |
| `VeriPyAsm/Embedding.lean` | Shallow translation and correspondence proofs |
| `VeriPyAsm/Admission.lean` | Stack admission bound to the exact artifact and capacity |
| `VeriPyAsm/Bytecode.lean` | `bytecode%` and `admit_bytecode%` term elaborators |
| `VeriPyAsm/Examples/Bytecode.lean` | Five literal artifacts and certified embeddings |
| `tests/` | Kernel-checked regression cases and CPython conformance checks |
| `docs/BYTECODE.md` | Implemented slice, usage, and limitations |
| `docs/DESIGN.md` | Verification flow and proposed user interface |
| `docs/PROTOTYPE.md` | Design and implementation milestones |
| `docs/CRUSH.md` | Automation design, trust policy, and experiment results |
| `examples/python/triangular.py` | First planned program proof |
| `experiments/CrushObligations.lean` | Checked VC experiment, built with `lake build CrushObligations` |

The initial guarantee will be correctness under an explicit Lean operational
semantics. Correspondence with the actual CPython runtime is a separate
obligation, supported initially by source inspection and differential testing.
