import BytecodeTests

/-! Prefix decoding is tested through the artifact boundary, including its
translation and stack certificates. Padding uses ordinary cached instructions
so that extended jump distances do not require hundreds of filler opcodes. -/

namespace VeriPyAsm.Tests.ExtendedDecode

open Semantics CPython.V314 Embedding Examples

def wideConstantArtifact : Artifact :=
  { literalArtifact with
    code := [128, 0, 69, 1, 82, 0, 35, 0]
    constants := List.replicate 256 .none ++ [.int 4242] }

def wideConstant : StackAdmitted wideConstantArtifact :=
  admit_bytecode% wideConstantArtifact

example : decode wideConstantArtifact = .ok wideConstant.translation.code :=
  wideConstant.translation.decoded

example : wideConstant.translation.code.instructions =
    [⟨0, 2, 128, 0, .resume⟩,
     ⟨2, 6, 82, 256, .loadConst (.int 4242)⟩,
     ⟨6, 8, 35, 0, .returnValue⟩] := by decide +kernel

example : run (step wideConstant.translation.program) 3 {} =
    .halted (.returned (.int 4242) { pc := 6 }) := by decide +kernel

-- A store/load pair exercises slot 256 and resets the operand accumulator
-- between distinct prefixed instructions.
def wideLocalArtifact : Artifact :=
  { literalArtifact with
    code := [128, 0, 94, 7, 69, 1, 112, 0, 69, 1, 86, 0, 35, 0]
    constants := []
    localNames := List.replicate 256 "unused" ++ ["wide"] }

def wideLocal : StackAdmitted wideLocalArtifact :=
  admit_bytecode% wideLocalArtifact

example : fetch wideLocal.translation.code.instructions 4 =
    some ⟨4, 8, 112, 256, .storeFast 256⟩ := by decide +kernel

example : fetch wideLocal.translation.code.instructions 8 =
    some ⟨8, 12, 86, 256, .loadFastBorrow 256⟩ := by decide +kernel

example : observe wideLocalArtifact [] = .ok (.returned (.int 7)) := by decide +kernel

def wideCheckedArtifact : Artifact :=
  { wideLocalArtifact with code := [128, 0, 69, 1, 88, 0, 35, 0] }

def wideChecked : StackAdmitted wideCheckedArtifact :=
  admit_bytecode% wideCheckedArtifact

example : observe wideCheckedArtifact [] = .ok (.raised .unboundLocalError) :=
  by decide +kernel

example : Stack.Valid wideLocal.translation.code wideLocalArtifact.stackSize
    wideLocal.stack.heights := wideLocal.stack.valid

-- The prefix group starts at 4; its terminal LOAD_CONST is at 6.
def jumpToGroupArtifact : Artifact :=
  { wideConstantArtifact with code := [128, 0, 77, 0, 69, 1, 82, 0, 35, 0] }

example : observe jumpToGroupArtifact [] = .ok (.returned (.int 4242)) :=
  by decide +kernel

example : rejection { jumpToGroupArtifact with code := jumpToGroupArtifact.code.set 3 1 } =
    some ⟨2, "control-flow target 6 is not an instruction boundary"⟩ := by decide +kernel

-- A two-prefix group exposes both an interior prefix and its terminal opcode.
-- The entry jump is checked first, so huge constant/local tables are unnecessary.
example : rejection { literalArtifact with code := [128, 0, 77, 1, 69, 1, 69, 0, 77, 0] } =
    some ⟨2, "control-flow target 6 is not an instruction boundary"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 77, 2, 69, 1, 69, 0, 77, 0] } =
    some ⟨2, "control-flow target 8 is not an instruction boundary"⟩ := by decide +kernel

private def boolWords : List Nat := [39, 0, 0, 0, 0, 0, 0, 0]

-- Forward displacement begins after the terminal opcode, not at group start.
-- Unreachable TO_BOOL instructions are well encoded; stack admission only
-- propagates heights along reachable control flow.
def wideForwardArtifact : Artifact :=
  { literalArtifact with
    code := [128, 0, 69, 1, 77, 0] ++
      (List.replicate 64 boolWords).flatten ++ [94, 7, 35, 0]
    constants := [] }

def wideForward : StackAdmitted wideForwardArtifact :=
  admit_bytecode% wideForwardArtifact

example : fetch wideForward.translation.code.instructions 2 =
    some ⟨2, 6, 77, 256, .jump 518⟩ := by decide +kernel

example : run (step wideForward.translation.program) 4 {} =
    .halted (.returned (.int 7) { pc := 520 }) := by decide +kernel

-- Backward displacement also includes the terminal opcode's inline cache.
-- The boolean stack value survives every TO_BOOL and the backward edge.
def wideBackwardArtifact : Artifact :=
  { literalArtifact with
    code := [128, 0, 82, 0] ++ (List.replicate 63 boolWords).flatten ++
      [28, 0, 69, 1, 75, 0, 0, 0]
    constants := [.bool true] }

def wideBackward : StackAdmitted wideBackwardArtifact :=
  admit_bytecode% wideBackwardArtifact

example : fetch wideBackward.translation.code.instructions 510 =
    some ⟨510, 516, 75, 256, .jump 4⟩ := by decide +kernel

example : referenceStep wideBackward.translation.code { pc := 510, stack := [.bool true] } =
    .next { pc := 4, stack := [.bool true] } := by decide +kernel

example : observe wideBackwardArtifact [] 100 = .ok .exhausted := by decide +kernel

-- Conditional jumps compute their origin after their cache, too.
example : rejection { literalArtifact with code := [128, 0, 69, 1, 100, 0, 0, 0, 94, 1, 35, 0] } =
    some ⟨2, "control-flow target 520 is not an instruction boundary"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 69, 1, 75, 0, 0, 0] } =
    some ⟨2, "backward jump before start of code"⟩ := by decide +kernel

-- A byte matching EXTENDED_ARG inside a cache remains invalid cache payload.
example : rejection { add1Artifact with code := add1Artifact.code.set 8 69 } =
    some ⟨6, "expected zero baseline cache payload"⟩ := by decide +kernel

-- Malformed chains report physical byte offsets, before opcode interpretation.
example : rejection { literalArtifact with code := [128, 0, 69, 1] } =
    some ⟨2, "dangling EXTENDED_ARG"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 69, 0, 82, 0, 35, 0] } =
    some ⟨2, "leading EXTENDED_ARG must be nonzero"⟩ := by decide +kernel

example : rejection { literalArtifact with
    code := [128, 0, 69, 1, 69, 0, 69, 0, 69, 0, 82, 0] } =
    some ⟨8, "more than three EXTENDED_ARG prefixes"⟩ := by decide +kernel

example : rejection { literalArtifact with
    code := [128, 0, 69, 128, 69, 0, 69, 0, 82, 0] } =
    some ⟨8, "operand exceeds signed 32-bit range"⟩ := by decide +kernel

-- Unreachable malformed encodings are still rejected after a valid return.
example : rejection { literalArtifact with code := [128, 0, 94, 1, 35, 0, 69, 1] } =
    some ⟨6, "dangling EXTENDED_ARG"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 94, 1, 35, 0, 69, 0, 82, 0] } =
    some ⟨6, "leading EXTENDED_ARG must be nonzero"⟩ := by decide +kernel

-- Bounds and opcode-specific restrictions apply to the effective operand.
example : rejection { literalArtifact with code := [128, 0, 69, 1, 82, 0, 35, 0] } =
    some ⟨2, "constant index out of bounds"⟩ := by decide +kernel

example : rejection { add1Artifact with code := [128, 0, 69, 1, 86, 0, 35, 0] } =
    some ⟨2, "local index out of bounds"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 69, 1, 94, 0, 35, 0] } =
    some ⟨2, "LOAD_SMALL_INT operand must fit in one byte"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 69, 1, 35, 0] } =
    some ⟨2, "expected zero unused argument"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 69, 1, 28, 0, 35, 0] } =
    some ⟨2, "expected zero unused argument"⟩ := by decide +kernel

example : rejection { literalArtifact with code := [128, 0, 69, 1, 39, 0, 0, 0, 0, 0, 0, 0, 35, 0] } =
    some ⟨2, "expected zero unused argument"⟩ := by decide +kernel

#print axioms wideConstant
#print axioms wideLocal
#print axioms wideForward
#print axioms wideBackward

end VeriPyAsm.Tests.ExtendedDecode
