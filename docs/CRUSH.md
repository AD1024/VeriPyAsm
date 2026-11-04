# Using Crush in VeriPyAsm

Assessment date: 2026-11-04. Recommendation: use
[lean-crush](https://github.com/AD1024/lean-crush) as the first backend for
discharging verification conditions, while proving the bytecode semantics and
verification-condition generation rules independently in Lean.

The [verification-flow design](DESIGN.md) defines the current discharge policies,
per-obligation report, and manual proof registry with `rfl`-certified equality
between the supplied theorem type and generated VC. Both checked reconstruction and
explicit solver trust are supported in the design; the experiment uses checked mode.

Crush is a pinned Lake dependency so both builds and the VS Code Lean extension
can resolve the experiment's imports. The core library does not import Crush;
integration with actual bytecode verification conditions remains M3/M4 work.

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
or performance benchmark and not a proof about Python bytecode. Connecting these
obligations to the actual instructions remains M2/M3 work.

The Lake configuration and manifest pin Crush to
`26b00a788943619f3335fa8e8de1da8ce1ee4362`, with Lean 4.34.0. The package is
materialized under `.lake/packages/crush` and does not depend on a sibling
checkout or a machine-specific path.

With cvc5 on `PATH`, run from the VeriPyAsm project root:

```sh
lake build CrushObligations
```

`lake build` builds the core library. The experiment is a separate named target;
no automated test driver is configured yet. Lake also supplies its import paths
to VS Code, without a custom `LEAN_PATH` setting.

## Integration tasks

1. Prove the first bytecode loop with explicit semantic steps; apply Crush to the
   resulting pure obligations and record which hints are necessary.
2. Expose a narrow automation interface to the pinned Crush dependency, without
   making semantic definitions import solver machinery. Enforce the selected
   trust policy and report actual proof dependencies and backend provenance.
3. Prove sound block/loop VC rules, including exceptional exits, state validity,
   and the chosen termination condition. Automation must construct Lean proof
   terms applying these rules to the original artifact.
4. Maintain an obligation corpus: linear/nonlinear arithmetic, signed division,
   datatype/tag facts, heap updates, and later async transition invariants. Report
   translation, solver, reconstruction, and timeout failures separately.
5. Supply checked domain lemmas where a solver understands an operation but replay
   cannot justify it. Keep a clear path to ordinary Lean proofs for difficult goals.
6. Audit axioms and artifact identity in CI when the first program proofs land.
   Keep one execution test, one VC proof, and a whole-program correctness theorem
   as distinct kinds of evidence in project reporting.
