/-! Shared error type for wordcode parsing and artifact decoding. -/

namespace VeriPyAsm.CPython.V314

structure DecodeError where
  offset : Nat
  reason : String
  deriving Repr, DecidableEq

end VeriPyAsm.CPython.V314
