import VeriPyAsm.Examples.Triangular.Specification
import VeriPyAsm.Verification.VC.Generate

/-! Automatically generated VCs and conditional assembly for the original
triangular contract. Only the admitted bytes and native annotations are inputs;
no hand-written block summaries, assembly theorem, or VC provider are imported. -/

namespace VeriPyAsm.Examples.Triangular

def specification : Verification.VC.Specification Int where
  contract := triangularContract
  cutpoints := [6]
  invariant N _ := invariant N
  ranking := some (fun _ _ => rank)

veripy_generate generated from triangular for specification
  unfolding [triangularContract, postcondition, invariant, frame, rank]

end VeriPyAsm.Examples.Triangular
