import VeriPyAsm.Target
import VeriPyAsm.Semantics.Value

/-! Input supplied by an external extractor. This is a Lean literal interface,
not a .pyc/marshal or JSON loader. Provenance is recorded, not authenticated. -/

namespace VeriPyAsm.CPython.V314

open Semantics

inductive RuntimeProfile where
  /-- Baseline, single-threaded, no tracing/JIT/signals, sufficient resources. -/
  | baselineSequential
  | unsupported (description : String)
  deriving Repr, DecidableEq

structure Artifact where
  schemaVersion : Nat := 1
  implementation : String := "cpython"
  version : PythonVersion := targetPythonVersion
  profile : RuntimeProfile := .baselineSequential
  build : String
  optimize : Nat := 0
  name : String
  /-- Byte values stored as naturals so invalid literals are rejected, not truncated. -/
  code : List Nat
  constants : List Value
  argCount : Nat
  posOnlyArgCount : Nat := 0
  kwOnlyArgCount : Nat := 0
  localNames : List String
  names : List String := []
  freeVars : List String := []
  cellVars : List String := []
  stackSize : Nat
  flags : Nat := 3
  exceptionTable : List Nat := []
  deriving Repr, DecidableEq

end VeriPyAsm.CPython.V314
