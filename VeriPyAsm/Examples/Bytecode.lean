import VeriPyAsm.Bytecode

/-! Literal baseline artifacts from examples/python/bytecode_slice.py, CPython
3.14.4. The conformance test checks these against independently compiled code.
No universal functional-correctness claim is made here. -/

namespace VeriPyAsm.Examples

open Semantics CPython.V314 Embedding

def add1Artifact : Artifact :=
  { build := "3.14.4 (main, Apr  7 2026, 13:13:20) [Clang 16.0.0 (clang-1600.0.26.6)]"
    name := "add1"
    code := [128, 0, 86, 0, 94, 1, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0]
    constants := [.int 1]
    argCount := 1
    localNames := ["n"]
    stackSize := 2 }

def countdownArtifact : Artifact :=
  { add1Artifact with
    name := "countdown"
    code := [128, 0, 86, 0, 94, 0, 56, 148, 0, 0, 100, 12, 0, 0, 28, 0,
      86, 0, 94, 1, 44, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 0,
      75, 18, 0, 0, 86, 0, 35, 0]
    constants := [.int 0] }

def chooseArtifact : Artifact :=
  { add1Artifact with
    name := "choose"
    code := [128, 0, 86, 0, 39, 0, 0, 0, 0, 0, 0, 0, 100, 3, 0, 0,
      28, 0, 86, 1, 35, 0, 86, 2, 35, 0]
    constants := [.none]
    argCount := 3
    localNames := ["flag", "x", "y"]
    stackSize := 1 }

def checkedArtifact : Artifact :=
  { add1Artifact with
    name := "checked"
    code := [128, 0, 86, 0, 39, 0, 0, 0, 0, 0, 0, 0, 100, 3, 0, 0,
      28, 0, 94, 1, 112, 1, 88, 1, 35, 0]
    localNames := ["flag", "x"]
    stackSize := 1 }

def literalArtifact : Artifact :=
  { add1Artifact with
    name := "literal"
    code := [128, 0, 82, 0, 35, 0]
    constants := [.int 1000]
    argCount := 0
    localNames := []
    stackSize := 1 }

/-- The elaborator produces both decoding and step-correspondence certificates. -/
def add1 : Translation add1Artifact := bytecode% add1Artifact
def countdown : Translation countdownArtifact := bytecode% countdownArtifact
def choose : Translation chooseArtifact := bytecode% chooseArtifact
def checked : Translation checkedArtifact := bytecode% checkedArtifact
def literal : Translation literalArtifact := bytecode% literalArtifact

theorem add1_representation : step add1.program = referenceStep add1.code := add1.correct

example : run (step add1.program) 5 { locals := [some (.int 41)] } =
    .halted (.returned (.int 42) { pc := 18, locals := [some (.int 41)] }) := by
  decide

example : run (step countdown.program) 100 { locals := [some (.int 3)] } =
    .halted (.returned (.int 0) { pc := 40, locals := [some (.int 0)] }) := by
  decide +kernel

end VeriPyAsm.Examples
