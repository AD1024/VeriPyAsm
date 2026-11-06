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
- **Automatic verification conditions (VCs).** Generate Lean propositions from
  admitted bytecode and Lean specifications. A Python comment frontend supports
  integer contracts and sequential or nested loops, with checked source mapping.
- **Crush automation and manual proofs.** Discharge VCs with
  [lean-crush](https://github.com/AD1024/lean-crush), or register a theorem with
  `@[veripy_proof VC.name]`. Registration checks exact statement matching through
  an equality proof by `rfl`. Unresolved obligations are emitted as complete
  theorem statements for the user to prove.
- **Auditable results.** Reports identify the proof provider, observed solver
  backend, and axiom dependencies for each obligation. A final `VerifiedArtifact`
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

Generation emits a Lean module and a companion `.source.json` file. The separate
[proof module](VeriPyAsm/Examples/SourceTriangular/Proofs.lean) discharges the VCs
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
future work. The source frontend currently requires at least one `while` loop;
source assertion checkpoints and ghost hints are not yet supported. Native
bytecode assertions support bare `assert` with modeled scalar tests; message
constructors, `NOP`-folded assertions, and optimized artifacts are rejected.

Proofs establish properties of the explicit Lean semantics. Correspondence with
the CPython runtime is a separate obligation, currently supported by source
inspection and differential tests rather than a formal runtime refinement proof.
