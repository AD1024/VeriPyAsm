# VeriPyAsm

VeriPyAsm will verify Python programs by proving properties of their compiled
CPython bytecode in Lean 4. The long-term target includes mutable objects,
exceptions, library calls, and asynchronous programs.

**Status:** scalar bytecode, stack/ownership admission, and sequential contracts are implemented.
`bytecode% artifact` decodes CPython 3.14.4 baseline bytes and produces a certified
translation into shallow Lean commands. `admit_bytecode% artifact` also checks
stack requirements, consistent heights across control flow, exact return shape,
and the artifact's declared stack capacity. It also rejects overwriting a local
with a live borrow or storing borrowed values, including fused instructions.
Separate certificates support kernel-checked stack and ownership-protocol proofs.
See the [bytecode guide](docs/BYTECODE.md)
for the precise guarantees and remaining limits. Fused local instructions and
extended operands are supported. The compiled `triangular` loop has a stack
certificate and a universal total-correctness proof: every nonnegative integer
input `N` returns an integer `r` with `2*r = N*(N+1)`, without exceptions or VM faults.

The [contract interface](docs/CONTRACTS.md) now has a universal total-correctness
proof for the imported `add1` artifact: every integer input returns its successor,
preserves its local, and terminates without Python exceptions or VM faults.
Scoped `{ P } S { Q }` and `{{ P }} S {{ Q }}` notation expresses partial and
total correctness with frame predicates, including operand-stack conditions.
The explicit `returns Q` postcondition also observes the returned value;
`Examples/Add1.lean` uses this form for its successor guarantee.
The [instruction, block, and loop rules](docs/RULES.md) derive these proofs by
composition, with explicit continuation, return, and exception postconditions.
Loop termination uses a well-founded ranking between successive invariant states.
The triangular proof now exposes four named, closed VCs and a conditional assembly
theorem. Ordinary Lean proofs discharge those VCs in a separate module.
An optional Crush target resolves an annotated ranking proof, automatically proves
the remaining VCs with checked reconstruction, and assembles the artifact contract.
`VerifiedArtifact` combines the contract proof with both admission certificates
and a proof that every contract pre-state satisfies the call-entry assumptions.
Both `add1_verified` and `triangular_verified` expose this final package.

The [verification-flow design](docs/DESIGN.md) documents the implemented
`@[veripy_proof ...]` exact-match registry, `veripy_vcs` manifests,
`veripy_discover` handoffs, and `veripy_verify` final packages. Reports contain
complete pending statements, proof providers, actual backend events when available,
axiom dependencies, and aggregate assurance. Import `VeriPyAsm.Automation.Crush`
to enable automatic discharge; checked mode is the default, with explicit
`solver_trusted` configuration available. The current VCs are extracted by hand;
a full specification DSL and automatic VC generation remain planned.
Stack admission establishes structural properties;
functional correctness and exception freedom require separate contract proofs.

The [prototype plan](docs/PROTOTYPE.md) specifies the first Python fragment,
normal and exceptional contracts, termination obligations, artifact provenance,
validation strategy, and the staged route to async verification.

The [Crush integration guide](docs/CRUSH.md) records the checked artifact proof,
the earlier standalone experiment, and the remaining automation work.

## Build

The project pins **Lean 4.34.0** and a reviewed Crush revision through Lake.
With that toolchain installed through Elan, build the core library with:

```sh
lake build
```

The core and public example exports run a failing transitive axiom audit.
For the complete CI check, with CPython 3.14.4 available as `python3`, run:

```sh
make check
```

This discovers all project modules and regression libraries, builds them, audits
safe declarations (including certificate definitions), and runs the CPython
conformance harness. `make check-crush` also requires cvc5 and checks the Crush
targets, including discharge/trust-policy regressions. Set `PYTHON=/path/to/python3.14`
if the pinned interpreter has another name.

Check bytecode examples, admission/rejection cases, and proof dependencies with:

```sh
lake build BytecodeTests StackCertificateTests StackTests AdmissionTests
lake build OwnershipTests
lake build FusedSemanticsTests WordcodeTests ExtendedDecodeTests FusedDecodeTests
lake build ContractTests HoareTests BlockTests InstructionTests
lake build LoopTests TriangularTests VCAssemblyTests VerifiedArtifactTests
lake build AxiomAuditTests VCRegistryTests VCDischargeTests
python3 tests/check_cpython.py  # requires CPython 3.14.4
```

The Python check compares real code objects and normal/exceptional outcomes with
the Lean model and checks stack/ownership admission for the corpus. It is a test oracle,
not a production source-to-bytecode tool.

To check the Crush proof of the imported triangular artifact and the five
standalone examples, with cvc5 1.3.4 or a compatible version on `PATH`:

```sh
lake build TriangularCrush CrushObligations VCDischargeCrush
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
| `VeriPyAsm/CPython/V314/Ownership/` | Borrow provenance, live-owner checks, certificate analysis and soundness |
| `VeriPyAsm/Embedding.lean` | Shallow translation and correspondence proofs |
| `VeriPyAsm/Admission.lean` | Stack and ownership admission bound to the exact artifact; lower-level stack-only interface |
| `VeriPyAsm/Bytecode.lean` | `bytecode%` and `admit_bytecode%` term elaborators |
| `VeriPyAsm/Verification/` | Contracts, instruction/block/loop rules, partial/total correctness, artifact transport |
| `VeriPyAsm/Verification/VerifiedArtifact.lean` | Final packages enforcing admission, entry compatibility, and correctness |
| `VeriPyAsm/Verification/AxiomAudit.lean` | Shared failing check of transitive proof dependencies |
| `VeriPyAsm/Verification/VC/` | Exact registration, manifests, policy, complete handoffs, reports, and package assembly |
| `VeriPyAsm/Automation/Crush.lean` | Optional configurable Crush adapter with observed backend provenance |
| `VeriPyAsm/Examples/Bytecode.lean` | Five literal artifacts and certified embeddings |
| `VeriPyAsm/Examples/Add1.lean` | Universal total-correctness proof for imported integer `add1` |
| `VeriPyAsm/Examples/Triangular.lean` | Public entry point for the imported loop and its universal total-correctness theorem |
| `VeriPyAsm/Examples/Triangular/` | Artifact, symbolic blocks, closed VCs, conditional assembly, and separate arithmetic proofs |
| `tests/` | Kernel-checked regression cases and CPython conformance checks |
| `scripts/check.py`, `Makefile` | Complete CI entry point with automatic module/test discovery |
| `docs/BYTECODE.md` | Implemented slice, usage, and limitations |
| `docs/CONTRACTS.md` | Contract interface, execution rules, universal program proofs |
| `docs/RULES.md` | Sound instruction/block/loop rules, continuation boundaries, invariant and ranking proofs |
| `docs/DESIGN.md` | Verification flow, implemented commands, and future generation interface |
| `docs/PROTOTYPE.md` | Design and implementation milestones |
| `docs/CRUSH.md` | Automation design, trust policy, and experiment results |
| `examples/python/triangular.py` | Source example for the first verified bytecode loop |
| `experiments/CrushObligations.lean` | Checked VC experiment, built with `lake build CrushObligations` |
| `experiments/TriangularCrush.lean` | Checked Crush proofs of the actual loop VCs, assembled into artifact total correctness |
| `experiments/VCDischargeCrush.lean` | Solver failure isolation and checked/solver-trusted policy regressions |

The guarantees are relative to the explicit Lean operational semantics.
Correspondence with the actual CPython runtime is a separate
obligation, supported initially by source inspection and differential testing.
