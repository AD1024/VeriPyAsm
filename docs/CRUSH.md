# Using Crush in VeriPyAsm

Assessment date: 2026-11-04. Recommendation: use
[lean-crush](https://github.com/AD1024/lean-crush) as the first backend for
discharging verification conditions, while proving the bytecode semantics and
verification-condition generation rules independently in Lean.

The [verification-flow design](DESIGN.md) defines the current discharge policies,
per-obligation report, and manual proof registry with `rfl`-certified equality
between the supplied theorem type and generated VC. Both checked reconstruction and
explicit solver trust are supported in the design; the current examples use checked mode.

Crush is a pinned Lake dependency so both builds and the VS Code Lean extension
can resolve the imports. The core library does not import Crush. The separate
`TriangularCrush` target now proves the actual loop VCs and assembles correctness
of the imported artifact. Automatic generation, proof registration, configurable
discharge policies, and per-obligation reporting remain prototype work.

## Where it fits

The proposed pipeline is:

```text
actual code object
  -> checked decoding and admission
  -> Lean operational semantics
  -> symbolic execution using proved block/loop rules
  -> verification conditions
  -> Crush reconstruction + ordinary Lean proofs
  -> theorem about the imported artifact
```

The mathematical contract and loop invariants are inputs to this process. Crush
does not supply a Python semantics, infer all invariants, establish termination
without a measure, or prove our VC generator sound.

| Project need | Proposed use of Crush | Proof work outside the backend |
| --- | --- | --- |
| Scalar bytecode | Local-value equalities, branch conditions, arithmetic, datatype cases | Correct instruction and Python operation rules |
| Loops | Invariant initialization/preservation/exit and ranking-function side conditions | Invariant discovery, loop-rule soundness, induction/well-foundedness |
| Mutable containers | Bounds, read/write equalities, quantified invariants, frame side conditions | Heap semantics, aliasing/ownership rules, abstraction lemmas |
| Function contracts | Instantiate summaries and higher-order predicates | Bind callees to their actual implementation and model effects |
| Async safety | Preserve an invariant for each scheduler/cancellation transition | Coroutine/runtime semantics, admitted schedules, induction over executions |
| Async liveness | Arithmetic or logical subgoals within a progress argument | Fairness assumptions, responsiveness assumptions, temporal/ranking proofs |

The repository's [Loom case study](https://github.com/AD1024/lean-crush/blob/main/Test/CaseStudies/Loom.lean)
already examines the same architecture: a verifier generates VCs, then swaps its
solver backend. Its examples include arithmetic and quantified functional-array
obligations. They are representative ported goals, not an integrated Python or
Loom verifier. Use them as guidance for expressing our residual obligations.

Higher-order support is useful for pure reference functions, summaries, and
predicates. An effectful Python callback must still have a contract over state
and outcomes; it cannot be replaced by a pure mathematical function without a
proved abstraction or an explicit assumption.

## Configurable proof policy

The reviewed [configuration](https://github.com/AD1024/lean-crush/blob/main/Crush/Frontend/Config.lean)
defaults to solver trust. A trusted SMT discharge introduces `Crush.crushSorry`.
VeriPyAsm's default checked mode must explicitly require reconstruction:

```lean
import Crush

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct.trustBvDecide false
set_option crush.reconstruct.trustNativeDecide false
```

An explicit `solver_trusted` mode sets `crush.trust "trust"`; its results may
depend on `Crush.crushSorry` and must be labeled solver-trusted in both per-VC and
aggregate reports. Do not silently fall back from checked mode to trust after a
failure. A failure leaves an obligation for another proof or a deliberate policy
change. Keep environmental contracts as theorem premises and audit transitive
axiom dependencies, including manually registered proofs. Reject `sorryAx` in
either mode. Reconstruction rejects admission/trust axioms, but ordinary
user-declared axioms remain assumptions unless separately excluded by our policy.
[Kernel checker](https://github.com/AD1024/lean-crush/blob/main/Crush/Solver/KernelCheck.lean)

cvc5 offers Alethe replay as well as core-based reconstruction; the automatic
portfolio can choose either. A successful checked proof does not establish that
Alethe replay specifically succeeded. Measure replay separately when debugging
that path. Solver success may also exceed reconstruction coverage. [README](https://github.com/AD1024/lean-crush#requiring-checked-proofs)

Initially use standard Lean values and proved rewrite/summary lemmas. Introduce
custom lowerings or replay extensions only for a demonstrated gap, with semantics
lemmas and checks against the original Lean proposition. In particular, do not
map Python signed division/remainder directly to an SMT operation without proving
the sign conventions match and preserving the zero-divisor exceptional branch.
Use `Int` for Python integers; reserve bitvectors for bytecode fields and operations
whose fixed-width interpretation has been justified.

## Initial experiment

[`CrushObligations.lean`](../experiments/CrushObligations.lean) contains five named
theorems, each proved with `by crush` under the strict options above:

1. The loop counter remains nonnegative and decreases.
2. The triangular-number invariant holds at initialization.
3. The nonlinear invariant is preserved by `s := s + n; n := n - 1`.
4. The invariant implies the postcondition on loop exit.
5. A functional update preserves an unrelated location.

All five checked successfully using Lean 4.34.0 and cvc5 1.3.4 with a five-second
per-query solver timeout. `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound` for each theorem. Neither `sorryAx` nor
`Crush.crushSorry` occurred. This is a small feasibility experiment, not a coverage
or performance benchmark and not a proof about Python bytecode. The separate
artifact proof below now supplies that connection for the triangular loop.

The Lake configuration and manifest pin Crush to
`26b00a788943619f3335fa8e8de1da8ce1ee4362`, with Lean 4.34.0. The package is
materialized under `.lake/packages/crush` and does not depend on a sibling
checkout or a machine-specific path.

With cvc5 on `PATH`, run from the VeriPyAsm project root:

```sh
lake build CrushObligations
```

`lake build` builds the core library. The experiment is a separate named target.
Lake also supplies its import paths to VS Code, without a custom `LEAN_PATH`
setting. The README lists the separate regression targets.

## Imported triangular artifact

[`TriangularCrush.lean`](../experiments/TriangularCrush.lean) imports the conditional
assembly and supplies proofs of the four closed propositions in
[`Triangular/VC.lean`](../VeriPyAsm/Examples/Triangular/VC.lean):

| VC | Checked proof script after introducing the binders |
| --- | --- |
| `loop6.init` | `crush` |
| `loop6.preserve` | `crush` |
| `loop6.exit` | `crush` |
| `loop6.decrease` | `rw [Int.toNat_lt_toNat positive]`, then `crush` |

The exit VC establishes both the zero counter and the result equation. A direct
Crush call on the original ranking goal returned `unknown`; the proved rewrite
converts its `Nat` comparison to integer arithmetic before discharge. It leaves
the named VC unchanged and introduces no additional premise.

The target imports neither `Arithmetic.lean` nor the existing unconditional
correctness theorem. `Triangular.CrushProofs.artifact_total` applies the same
`Assembly.artifact_total` theorem to the new proof bundle. Its conclusion is
`ArtifactTotalCorrect triangularArtifact triangularContract`, bound to the exact
imported bytes through the representation certificate.
`Triangular.CrushProofs.verified` additionally supplies the public verified
package, including stack/ownership admission and entry compatibility.

```sh
lake build TriangularCrush
```

All four VCs and the assembled artifact theorem checked with Lean 4.34.0 and
cvc5 1.3.4 under the strict options above and a five-second solver timeout.
The target audits their complete axiom dependency closures and fails on anything
outside `propext`, `Classical.choice`, and `Quot.sound`. This includes rejecting
`sorryAx`, `Crush.crushSorry`, and native-decision axioms.
Both experiment targets now use the shared `Verification/AxiomAudit.lean`
checker. `make check-crush` includes them in the full regression/audit/CPython
check; `make check` runs that suite without requiring an external SMT solver.

These are hand-extracted VCs with an explicit Crush proof provider. The target
prints theorem axiom dependencies; it does not yet implement the designed
proof-provider registry, pending-goal export, or backend-routing report. The cvc5
configuration alone is not evidence of which internal reconstruction path ran.

## Integration tasks

The first loop, sound instruction/block/loop rules, named VCs, conditional
assembly, and checked Crush proofs are implemented. Remaining steps:

1. Register proofs by VC name with a kernel-checked `rfl` certificate for the
   complete theorem type; reject mismatches and duplicate registrations.
2. Expose a configurable automation interface to the pinned Crush dependency, without
   making semantic definitions import solver machinery. Enforce the selected
   trust policy, report actual proof dependencies and backend provenance, and
   export exact pending statements.
3. Automate the current extraction and assembly by applying the proved rules to
   annotated artifacts, retaining exceptional exits and termination conditions.
4. Maintain an obligation corpus: linear/nonlinear arithmetic, signed division,
   datatype/tag facts, heap updates, and later async transition invariants. Report
   translation, solver, reconstruction, and timeout failures separately.
5. Supply checked domain lemmas where a solver understands an operation but replay
   cannot justify it. Keep a clear path to ordinary Lean proofs for difficult goals.
6. Keep execution tests, VC proofs, and whole-program correctness theorems
   distinct in reporting. The shared failing audit and `make check` CI entry
   point now cover proof assumptions and artifact-identity regressions.
