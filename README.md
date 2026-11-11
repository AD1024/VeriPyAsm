# VeriPyAsm

VeriPyAsm verifies Python programs at the bytecode level in **Lean 4**. It
translates CPython bytecode into a shallow Lean model, generates verification
conditions from program specifications, and combines their proofs into a verified
artifact.

The goal is to support real-world Python, eventually including mutable objects,
library calls, exception handling, and asynchronous programs. The current
prototype targets **CPython 3.14.4** and a sequential scalar fragment: integers,
booleans, `None`, local variables, arithmetic, comparisons, branches, and loops.

## Features

- **Certified bytecode translation.** Decode baseline CPython bytecode, including
  extended operands and fused local instructions, with a proof that the shallow
  translation agrees with the decoded reference semantics.
- **Checked admission.** Validate stack heights, declared stack capacity, return
  shape, and borrowed-reference lifetimes. The ownership checker conservatively
  rejects overwriting a local with a live borrow or storing a borrowed value.
- **Contracts and loop proofs.** Specify preconditions, return values, final
  stacks, and permitted exceptions. Prove partial correctness or total correctness
  using instruction and block rules, loop invariants, and termination measures.
  Bare assertion bytecode has explicit `AssertionError` semantics.
  Native logical checkpoint rules separate an incoming claim from the suffix
  that uses it, while preserving finite execution and loop progress.
- **Automatic verification conditions (VCs).** Generate Lean propositions from
  admitted bytecode and Lean specifications. A Python comment frontend supports
  integer contracts and sequential or nested loops, with checked source mapping.
  Scoped loops have separate initialization, preservation, ranking, and exit
  obligations. Runtime assertions and `# veripy: prove` hints also have mandatory
  obligations, including inside and after nested loops.
- **Crush automation and manual proofs.** Discharge VCs with
  [lean-crush](https://github.com/AD1024/lean-crush), or register a theorem with
  `@[veripy_proof VC.name]`. Registration checks exact statement matching through
  an equality proof by `rfl`. Unresolved obligations are emitted as complete
  theorem statements for the user to prove.
- **Auditable results.** Reports identify source spans, quantified assumptions,
  checkpoint dependencies, the proof provider, observed solver backend, and
  axiom dependencies for each obligation. A final `VerifiedArtifact`
  combines admission certificates, contract entry assumptions, and correctness.

Checked proof reconstruction is the default for VeriPyAsm's Crush adapter.
Explicit `solver_trusted` mode is also available and is labeled in the reports.
Transitive axiom audits enforce the selected policy.

## Setup

| Tool | Version | Needed for |
| --- | --- | --- |
| Lean and Lake, managed by Elan | **4.34.0** | Building the library and checking proofs |
| CPython | **3.14.4 exactly** | Source extraction and the full test suite |
| cvc5 | **1.3.4 tested** | Optional Crush automation and solver tests |

Install Git and [Lean via Elan](https://lean-lang.org/install/manual/), then run
from the repository root:

```sh
lake build
```

Elan uses the version in [lean-toolchain](lean-toolchain). Lake fetches the pinned
Crush dependency automatically. The core build needs neither Python nor an SMT
solver.

For source extraction and tests, install
[CPython 3.14.4](https://www.python.org/downloads/release/python-3144/) and check
that `python3 --version` reports that exact release. The Python tools use only
the standard library; there are no pip dependencies.

For automation, install [cvc5 1.3.4](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.3.4),
put the `cvc5` executable on `PATH`, and build the Crush examples:

```sh
cvc5 --version
lake build TriangularCrush GeneratedTriangularCrush
```

In VS Code, install the Lean 4 extension and open the repository root as a folder.
Lake supplies the dependency import paths, including Crush's.

## Try an example

The [annotated triangular example](examples/python/triangular_annotated.py)
specifies a sum and its termination measure directly in Python comments:

```python
# veripy: requires is_int(n) and n >= 0
# veripy: ensures is_int(result) and 2*result == old(n)*(old(n)+1)
def triangular(n):
    s = 0
    # veripy: loop sum_loop
    # veripy: invariant n >= 0
    # veripy: invariant 2*s + n*(n+1) == old(n)*(old(n)+1)
    # veripy: decreases n
    while n > 0:
        s = s + n
        n = n - 1
    return s
```

With CPython 3.14.4, generate its bytecode artifact, specification, and VCs, then
check the supplied Lean proofs:

```sh
python3 -m veripy_frontend generate examples/python/triangular_annotated.py \
  --function triangular --namespace VeriPyAsm.Examples.SourceTriangular \
  --output VeriPyAsm/Examples/SourceTriangular/Generated.lean
lake build VeriPyAsm.Examples.SourceTriangular.Proofs
```

Generation emits a Lean module and a companion `.source.json` file containing the
original source bytes and each attached directive's text, location, and target.
The separate [proof module](VeriPyAsm/Examples/SourceTriangular/Proofs.lean) discharges the VCs
and assembles the verified artifact; generating VCs alone does not prove the
contract. For every nonnegative integer input `N`, the example proves termination
with an integer result `r` satisfying `2*r = N*(N+1)`, without exceptions or VM
faults, under the Lean semantics.

See also the [nested-loop multiplication example](examples/python/nested_product_annotated.py)
and the [Crush proof of generated VCs](experiments/GeneratedTriangularCrush.lean).
Tools that already produce bytecode artifacts can use
[`admit_bytecode%`](VeriPyAsm/Bytecode.lean) and Lean specifications directly.
The [native assertion examples](VeriPyAsm/Examples/Assertions/Correctness.lean)
prove both exception-free behavior under a precondition and contracts that
explicitly permit assertion failure.
The [native checkpoint example](VeriPyAsm/Examples/Checkpoints/VC.lean) separates
runtime-assertion, logical-hint, and return obligations in an explicit manifest.
It has [manual proofs](VeriPyAsm/Examples/Checkpoints/Correctness.lean) and an
[alternate Crush provider](experiments/CheckpointCrush.lean); build the latter
with `lake build CheckpointCrush`.

The [source checkpoint example](examples/python/triangular_checkpoints.py) adds
a named runtime assertion and a logical conservation hint to the triangular loop:

```sh
python3 -m veripy_frontend inspect examples/python/triangular_checkpoints.py --function triangular
python3 -m veripy_frontend generate examples/python/triangular_checkpoints.py \
  --function triangular --namespace VeriPyAsm.Examples.SourceCheckpoints \
  --output VeriPyAsm/Examples/SourceCheckpoints/Generated.lean
lake build VeriPyAsm.Examples.SourceCheckpoints.Proofs SourceCheckpointCrush
```

It maps bare `assert`, optional `# veripy: name A`, and `# veripy: prove H: P`
to checked bytecode regions and edges. Its five VCs cover entry, initialization,
loop preservation/termination, the runtime assertion, and the logical hint.
The companion JSON links checkpoint labels and source spans to their Lean goals.
[Manual](VeriPyAsm/Examples/SourceCheckpoints/Proofs.lean) and
[Crush](experiments/SourceCheckpointCrush.lean) providers verify the same generated
specification. Generation alone does not establish a checkpoint claim.

Checkpoints also compose through scoped and nested loops. The
[nested multiplication example](examples/python/nested_product_checkpoints.py)
resets its inner counter on each outer iteration and checks facts both inside
and after the inner loop. Its fifteen mandatory VCs cover entry, execution safety,
four requirements per loop, and five named checkpoints:

```sh
lake build VeriPyAsm.Examples.SourceNestedCheckpoints.Proofs SourceNestedCheckpointCrush
```

Loop exits retain downstream checkpoint obligations. A hint refers to the frame
where it was proved; it does not become an invariant of a summarized loop.
For example, a bad inner measure leaves `generated.VC.loop_28_ranking` pending
while independent obligations can be proved. Final assembly still requires every
VC. The [mixed Crush/manual example](experiments/ScopedLoopCrush.lean), built with
`lake build ScopedLoopCrush`, uses Crush for invariants and exits and exact manual
proofs for the integer-to-natural ranking conversions.

## Run the checks

```sh
make check        # Lean regressions, axiom audits, CPython comparisons, frontend tests
make check-crush  # All of the above, plus Crush/solver tests
```

Both commands require CPython 3.14.4; `check-crush` also requires cvc5 on `PATH`.
If the interpreter has a different name or location, use
`make check PYTHON=/path/to/python3.14` (or the same override with `check-crush`).

## Current limits

The prototype supports a defined scalar bytecode fragment. General objects,
heap mutation, function calls, exception handlers, and async execution remain
future work. The source frontend requires at least one `while` loop. Checkpoint
generation supports single, sequential, and nested loops, including scoped
locals that are initialized inside a loop. Native
bytecode assertions support bare `assert` with modeled scalar tests; message
constructors, `NOP`-folded assertions, and optimized artifacts are rejected.
