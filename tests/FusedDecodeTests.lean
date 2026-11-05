import VeriPyAsm.Examples.Triangular

namespace VeriPyAsm.Tests.FusedDecode

open Semantics CPython.V314 Examples

private def packedArtifact (opcode arg : Nat) : Artifact :=
  { add1Artifact with
    code := [128, 0, opcode, arg, 35, 0]
    localNames := ["first", "second"] }

private def decodedOp (artifact : Artifact) (pc : Nat) : Option Op :=
  match decode artifact with
  | .error _ => none
  | .ok code => (fetch code.instructions pc).map Instruction.op

private def rejection (artifact : Artifact) : Option DecodeError :=
  match decode artifact with
  | .error error => some error
  | .ok _ => none

example : decodedOp (packedArtifact 87 16) 2 =
    some (.loadFastBorrowLoadFastBorrow 1 0) := by decide
example : decodedOp (packedArtifact 89 1) 2 = some (.loadFastLoadFast 0 1) := by decide
example : decodedOp (packedArtifact 113 16) 2 = some (.storeFastLoadFast 1 0) := by decide
example : decodedOp (packedArtifact 114 1) 2 = some (.storeFastStoreFast 0 1) := by decide
example : decodedOp (packedArtifact 113 0) 2 = some (.storeFastLoadFast 0 0) := by decide
example : decodedOp (packedArtifact 114 17) 2 = some (.storeFastStoreFast 1 1) := by decide
example : decodedOp { packedArtifact 89 255 with localNames := List.replicate 16 "local" } 2 =
    some (.loadFastLoadFast 15 15) := by decide

example : rejection (packedArtifact 87 32) =
    some ⟨2, "first fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 87 2) =
    some ⟨2, "second fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 89 32) =
    some ⟨2, "first fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 89 2) =
    some ⟨2, "second fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 113 32) =
    some ⟨2, "first fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 113 2) =
    some ⟨2, "second fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 114 32) =
    some ⟨2, "first fused local index out of bounds"⟩ := by decide
example : rejection (packedArtifact 114 2) =
    some ⟨2, "second fused local index out of bounds"⟩ := by decide

-- Fused operands are packed nibbles, not an arbitrary extended first index.
example : rejection { packedArtifact 87 0 with code := [128, 0, 69, 1, 87, 0, 35, 0] } =
    some ⟨2, "fused local operands must fit in one byte"⟩ := by decide
example : rejection { packedArtifact 89 0 with code := [128, 0, 69, 1, 89, 0, 35, 0] } =
    some ⟨2, "fused local operands must fit in one byte"⟩ := by decide
example : rejection { packedArtifact 113 0 with code := [128, 0, 69, 1, 113, 0, 35, 0] } =
    some ⟨2, "fused local operands must fit in one byte"⟩ := by decide
example : rejection { packedArtifact 114 0 with code := [128, 0, 69, 1, 114, 0, 35, 0] } =
    some ⟨2, "fused local operands must fit in one byte"⟩ := by decide

example : decodedOp triangularArtifact 20 = some (.loadFastBorrowLoadFastBorrow 1 0) := by
  decide +kernel
example : Stack.Valid triangular.translation.code triangularArtifact.stackSize triangular.stack.heights :=
  triangular.stack.valid

example : run (step triangular.translation.program) 100
    { locals := [some (.int (-3)), none] } =
    .halted (.returned (.int 0) { pc := 60, locals := [some (.int (-3)), some (.int 0)] }) := by
  decide +kernel

#print axioms triangular
#print axioms triangular_no_underflow

end VeriPyAsm.Tests.FusedDecode
