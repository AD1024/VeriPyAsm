/-!
# Interpreter target

The prototype targets one exact CPython release. These declarations record the
intended target; they do not assert that any instructions are implemented or that
the future semantics agrees with CPython.
-/

namespace VeriPyAsm

/-- A Python interpreter release, without platform or build configuration. -/
structure PythonVersion where
  major : Nat
  minor : Nat
  patch : Nat
  deriving Repr, DecidableEq

/-- The implementation whose bytecode the prototype will model. -/
def targetImplementation : String := "cpython"

/-- The pinned interpreter release for the first prototype. -/
def targetPythonVersion : PythonVersion :=
  { major := 3, minor := 14, patch := 4 }

end VeriPyAsm
