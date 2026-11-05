import VeriPyAsm.Examples.Bytecode

/-! The pinned triangular artifact, its stack certificate, and bounded execution
examples. Functional correctness is proved in the separate Correctness module.
The conformance harness checks these stored bytes against CPython. -/

namespace VeriPyAsm.Examples

open Semantics CPython.V314

def triangularArtifact : Artifact :=
  { add1Artifact with
    name := "triangular"
    code := [128, 0, 94, 0, 112, 1, 86, 0, 94, 0, 56, 148, 0, 0, 100, 20,
      0, 0, 28, 0, 87, 16, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 1,
      86, 0, 94, 1, 44, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 0,
      75, 26, 0, 0, 86, 1, 35, 0]
    constants := [.int 0]
    localNames := ["n", "s"] }

def triangular : StackAdmitted triangularArtifact := admit_bytecode% triangularArtifact

theorem triangular_no_underflow (fuel : Nat) (locals : List (Option Value))
    (failureFrame : Frame) :
    run (step triangular.translation.program) fuel { locals } ≠
      .halted (.fault .stackUnderflow failureFrame) :=
  triangular.run_no_underflow fuel locals failureFrame

example : run (step triangular.translation.program) 100
    { locals := [some (.int 3), none] } =
    .halted (.returned (.int 6) { pc := 60, locals := [some (.int 0), some (.int 6)] }) := by
  decide +kernel

example : run (step triangular.translation.program) 20
    { locals := [some (.int 0), none] } =
    .halted (.returned (.int 0) { pc := 60, locals := [some (.int 0), some (.int 0)] }) := by
  decide +kernel

end VeriPyAsm.Examples
