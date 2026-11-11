/-! Diagnostic boundaries in a weakest precondition. `requirement` is the
identity on propositions: adding or removing a boundary is justified by `rfl`.
The generator retains these boundaries while normalizing, then reconstructs
the original proposition from separately named obligations in the kernel. -/

namespace VeriPyAsm.Verification.VC

inductive RequirementKind where
  | initialization | preservation | ranking | exit
  deriving DecidableEq, BEq, Repr, Inhabited

def requirement (_header : Nat) (_kind : RequirementKind) (claim : Prop) : Prop := claim

end VeriPyAsm.Verification.VC
