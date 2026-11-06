import VeriPyAsm.Bytecode
import VeriPyAsm.Verification.AxiomAudit

/-! Literal CPython 3.14.4 artifacts from examples/python/assertions.py.
The conformance harness checks these fields against actual code objects. -/

namespace VeriPyAsm.Examples.Assertions

open CPython.V314

def nonnegativeArtifact : Artifact :=
  { build := "3.14.4 (main, Apr  7 2026, 13:13:20) [Clang 16.0.0 (clang-1600.0.26.6)]"
    name := "nonnegative"
    code := [128, 0, 86, 0, 94, 0, 56, 188, 0, 0, 103, 3, 0, 0,
      28, 0, 81, 0, 104, 1, 86, 0, 35, 0]
    constants := [.int 0]
    argCount := 1
    localNames := ["n"]
    stackSize := 2 }

def nonnegative : Admitted nonnegativeArtifact := admit_bytecode% nonnegativeArtifact

def alwaysFailsArtifact : Artifact :=
  { build := nonnegativeArtifact.build
    name := "always_fails"
    code := [128, 0, 81, 0, 104, 1]
    constants := [.bool false]
    argCount := 0
    localNames := []
    stackSize := 1 }

def alwaysFails : Admitted alwaysFailsArtifact := admit_bytecode% alwaysFailsArtifact

#veripy_audit VeriPyAsm.Examples.Assertions

end VeriPyAsm.Examples.Assertions
