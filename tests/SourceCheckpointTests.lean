import VeriPyAsm.Frontend.Checkpoint
import VeriPyAsm.Examples.Assertions.Artifact

namespace VeriPyAsm.Tests.SourceCheckpoint
open Frontend CPython.V314 Examples.Assertions Lean Elab Command

-- Explicit positions for the literal assertion fixture; source fidelity is a
-- frontend responsibility. Here we test the structural certificate itself.
private def assertionSpan : Span := ⟨2, 4, 2, 17⟩
private def returnSpan : Span := ⟨3, 4, 3, 12⟩
def source : Source where
  path := "assertion.py"
  digest := "structural-test"
  functionName := nonnegativeArtifact.name
  localNames := ["n"]
  positions := [none] ++ List.replicate 9 (some assertionSpan) ++ List.replicate 2 (some returnSpan)
  loop := ⟨"unused", assertionSpan, assertionSpan, returnSpan⟩

def assertion : CheckpointOrigin := ⟨"nonnegative", .assertion, assertionSpan⟩
def beforeReturn : CheckpointOrigin := ⟨"before_return", .before, returnSpan⟩
def afterAssertion : CheckpointOrigin := ⟨"after_assertion", .after, assertionSpan⟩
def origins := [assertion, beforeReturn, afterAssertion]

veripy_checkpoints mapped from nonnegative for source at origins

def assertionMap : CheckpointMapping :=
  ⟨2, [2, 4, 6, 10, 16, 18], [⟨0, 2⟩], [⟨10, 20⟩], [⟨0, 2⟩], [18]⟩

example : mapped = [assertionMap,
    ⟨20, [20, 22], [⟨10, 20⟩], [], [⟨10, 20⟩], []⟩,
    { assertionMap with boundaryEdges := [⟨10, 20⟩] }] := rfl

theorem checked : Checkpoint.checkAll nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights origins mapped = .ok () := mapped.valid

-- A success continuation never replaces the actual assertion failure path.
example : (Checkpoint.check nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights assertion { assertionMap with failureNodes := [] }).isOk = false := by decide +kernel

example : (Checkpoint.check nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights assertion { assertionMap with entryEdges := [] }).isOk = false := by decide +kernel

example : (Checkpoint.check nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights assertion { assertionMap with exitEdges := [] }).isOk = false := by decide +kernel

-- Cache/interior offsets, missing positions, and a terminal fallthrough fail.
example : (Checkpoint.check nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights assertion { assertionMap with entry := 8 }).isOk = false := by decide +kernel

example : (Checkpoint.infer nonnegativeArtifact { source with positions := source.positions.set 2 none }
    nonnegative.translation.code nonnegative.stack.heights assertion).isOk = false := by decide +kernel

example : (Checkpoint.infer nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights { beforeReturn with kind := .after }).isOk = false := by decide +kernel

example : (Checkpoint.checkAll nonnegativeArtifact source nonnegative.translation.code
    nonnegative.stack.heights [assertion, assertion] [assertionMap, assertionMap]).isOk = false := by decide +kernel

-- A prefixed instruction's terminal position selects its GROUP START. The
-- terminal opcode, prefix interior, and inline caches are never new boundaries.
def prefixedArtifact : Artifact where
  build := nonnegativeArtifact.build
  name := "prefixed"
  code := [128, 0, 69, 1, 82, 0, 35, 0]
  constants := List.replicate 257 (.int 0)
  argCount := 0
  localNames := []
  stackSize := 1
def prefixed : Admitted prefixedArtifact := admit_bytecode% prefixedArtifact
def prefixedSource : Source := { source with
  functionName := "prefixed", localNames := []
  positions := [none, some returnSpan, some assertionSpan, some returnSpan] }
def prefixedOrigins : List CheckpointOrigin := [⟨"load", .before, assertionSpan⟩]
veripy_checkpoints prefixedMap from prefixed for prefixedSource at prefixedOrigins
example : prefixedMap = [⟨2, [2], [⟨0, 2⟩], [⟨2, 6⟩], [⟨0, 2⟩], []⟩] := rfl

-- Conservatively refuse a region whose fused store could have swallowed the
-- requested source boundary, even though the bytecode itself is admitted.
def fusedArtifact : Artifact := { nonnegativeArtifact with
  name := "fused", code := [128, 0, 94, 1, 94, 2, 114, 1, 86, 0, 35, 0]
  argCount := 0, localNames := ["a", "b"], constants := [] }
def fused : Admitted fusedArtifact := admit_bytecode% fusedArtifact
def fusedSource : Source := { source with
  functionName := "fused", localNames := ["a", "b"]
  positions := [none] ++ List.replicate 3 (some assertionSpan) ++ List.replicate 2 (some returnSpan) }
example : Checkpoint.infer fusedArtifact fusedSource fused.translation.code fused.stack.heights
    ⟨"before_stores", .before, assertionSpan⟩ =
    .error "fused stores may erase the requested source boundary" := rfl

-- Publication is transactional even if the late certificate name collides.
def collision.valid : Nat := 7
/-- error: (kernel) constant has already been declared 'VeriPyAsm.Tests.SourceCheckpoint.collision.valid' -/
#guard_msgs in
veripy_checkpoints collision from nonnegative for source at origins
run_cmd do
  if (← getEnv).contains `VeriPyAsm.Tests.SourceCheckpoint.collision then
    throwError "failed checkpoint mapping retained a candidate"
  unless (← getEnv).contains `VeriPyAsm.Tests.SourceCheckpoint.collision.valid do
    throwError "failed checkpoint mapping removed an existing declaration"

#veripy_audit VeriPyAsm.Tests.SourceCheckpoint
end VeriPyAsm.Tests.SourceCheckpoint
