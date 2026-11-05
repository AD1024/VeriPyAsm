import VeriPyAsm.Verification.VC.Registry

namespace VeriPyAsm.Tests.VCRegistry.Fixture

def goal : Prop := ∀ n : Int, 0 ≤ n → n + 1 > n

@[veripy_proof goal]
theorem supplied (n : Int) (_nonnegative : 0 ≤ n) : n + 1 > n := by omega

end VeriPyAsm.Tests.VCRegistry.Fixture
