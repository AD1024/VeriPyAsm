import VeriPyAsm.Examples.SourceTriangular.Proofs

namespace VeriPyAsm.Tests.SourceMapping

open Frontend CPython.V314 Examples.SourceTriangular Lean Meta Elab Command

-- The header and complete region come from the source map, not a user offset.
example : sourceMap.header = 6 := rfl
example : sourceMap.testNodes = [6, 8, 10, 14] := rfl
example : sourceMap.backedges = [⟨54, 6⟩] := rfl
example : sourceMap.exitEdges = [⟨14, 58⟩] := rfl
example : check artifact source admitted.translation.code admitted.stack.heights sourceMap = .ok () :=
  sourceMap.valid

-- The source-only contract has an audited final artifact package.
example : Verification.VerifiedArtifact artifact contract := verified

-- Interior locations, stale metadata, and incomplete edge sets cannot be certified.
example : (check artifact source admitted.translation.code admitted.stack.heights
    { sourceMap with header := 8 }).isOk = false := by decide +kernel

example : (check artifact source admitted.translation.code admitted.stack.heights
    { sourceMap with header := 12 }).isOk = false := by decide +kernel

example : (check artifact source admitted.translation.code admitted.stack.heights
    { sourceMap with backedges := [] }).isOk = false := by decide +kernel

example : (check artifact { source with localNames := ["s", "n"] }
    admitted.translation.code admitted.stack.heights sourceMap).isOk = false := by decide +kernel

example : (check artifact { source with positions := source.positions.drop 1 }
    admitted.translation.code admitted.stack.heights sourceMap).isOk = false := by decide +kernel

example : (infer artifact { source with positions := List.replicate source.positions.length none }
    admitted.translation.code admitted.stack.heights).isOk = false := by decide +kernel

-- All source spans can be consistent while a separate cycle remains uncovered.
private def twoCycles : Code := { instructions := [
  ⟨0, 2, 0, 0, .jump 2⟩,
  ⟨2, 4, 0, 0, .popJumpIfTrue 2 4⟩,
  ⟨4, 6, 0, 0, .jump 4⟩] }

example : covered twoCycles 2 = false := by decide +kernel
example : covered admitted.translation.code sourceMap.header = true := by decide +kernel

-- Publishing the map and its certificate is transactional, including late
-- collisions with an existing certificate name.
def collision.valid : Nat := 7

/-- error: (kernel) constant has already been declared 'VeriPyAsm.Tests.SourceMapping.collision.valid' -/
#guard_msgs in
veripy_source collision from admitted for source

run_cmd do
  if (← getEnv).contains `VeriPyAsm.Tests.SourceMapping.collision then
    throwError "failed mapping retained its candidate declaration"
  unless (← getEnv).contains `VeriPyAsm.Tests.SourceMapping.collision.valid do
    throwError "failed mapping removed an existing declaration"

#veripy_audit VeriPyAsm.Tests.SourceMapping

end VeriPyAsm.Tests.SourceMapping
