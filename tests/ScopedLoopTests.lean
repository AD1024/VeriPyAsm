import VeriPyAsm.Examples.SourceNestedProduct.Proofs

namespace VeriPyAsm.Tests.ScopedLoops

open Frontend Examples.SourceNestedProduct Verification Verification.VC

set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

example : sourceMaps.parents = [none, some 0] := rfl
example : sourceMaps.loops.map Mapping.header = [10, 28] := rfl
example : checkForest artifact sources admitted.translation.code admitted.stack.heights sourceMaps = .ok () :=
  sourceMaps.valid
example : VerifiedArtifact artifact contract := verified

-- Both headers are necessary to cover this graph's cycles.
example : covered admitted.translation.code map0.header = false := by decide +kernel
example : coveredMany admitted.translation.code [map0.header, map1.header] = true := by decide +kernel
example : (checkForest artifact [source0] admitted.translation.code admitted.stack.heights
    { loops := [map0], parents := [none] }).isOk = false := by decide +kernel

-- Forest certificates reject forged parents, duplicate labels, missing edges,
-- and cross-loop regions, even when the artifact itself is admitted.
example : (checkForest artifact sources admitted.translation.code admitted.stack.heights
    { sourceMaps with parents := [none, none] }).isOk = false := by decide +kernel
example : (checkForest artifact [{ source0 with loop.body := source0.loop.statement }, source1]
    admitted.translation.code admitted.stack.heights sourceMaps).isOk = false := by decide +kernel
example : (checkForest artifact [source0, { source1 with loop.label := source0.loop.label }]
    admitted.translation.code admitted.stack.heights sourceMaps).isOk = false := by decide +kernel
example : (checkForest artifact sources admitted.translation.code admitted.stack.heights
    { sourceMaps with loops := [map0, { map1 with backedges := [] }] }).isOk = false := by decide +kernel
example : (checkForest artifact sources admitted.translation.code admitted.stack.heights
    { sourceMaps with loops := [map0, { map1 with bodyNodes := map0.header :: map1.bodyNodes }] }).isOk = false :=
  by decide +kernel

def missingInnerRank : ScopedSpecification (Int × Int) :=
  { specification with loops := [loop0, { loop1 with ranking := none }] }

/-- error: total correctness requires a ranking function for every scoped loop -/
#guard_msgs in
veripy_generate missingRank from admitted for missingInnerRank

#veripy_audit VeriPyAsm.Tests.ScopedLoops

end VeriPyAsm.Tests.ScopedLoops
