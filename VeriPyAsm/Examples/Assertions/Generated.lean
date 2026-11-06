import VeriPyAsm.Examples.Assertions.Artifact
import VeriPyAsm.Verification.VC.Generate

/-! Two contracts for the same assertion artifact: exclude failure under a
nonnegative precondition, or classify both outcomes for all integer inputs.
Both are generated from the bytes without a hand-written block summary. -/

namespace VeriPyAsm.Examples.Assertions

open Semantics Verification

namespace ExceptionFree

def contract : Contract Int where
  pre n initial := 0 ≤ n ∧ initial = { locals := [some (.int n)] }
  post n _ value final := value = .int n ∧ final.locals = [some (.int n)] ∧ final.stack = []
  raises _ _ _ _ := False

def specification : VC.Specification Int where
  contract := contract

veripy_generate generated from nonnegative for specification unfolding [contract]

end ExceptionFree

namespace WithFailure

def contract : Contract Int where
  pre n initial := initial = { locals := [some (.int n)] }
  post n _ value final :=
    0 ≤ n ∧ value = .int n ∧ final.locals = [some (.int n)] ∧ final.stack = []
  raises n _ exception final :=
    n < 0 ∧ exception = .assertionError ∧ final.locals = [some (.int n)] ∧
      final.stack = [.assertionErrorType]

def specification : VC.Specification Int where
  contract := contract

veripy_generate generated from nonnegative for specification unfolding [contract]

end WithFailure

#veripy_audit VeriPyAsm.Examples.Assertions

end VeriPyAsm.Examples.Assertions
