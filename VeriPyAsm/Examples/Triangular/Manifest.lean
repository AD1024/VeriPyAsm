import VeriPyAsm.Examples.Triangular.Assembly
import VeriPyAsm.Verification.VC.Manifest

/-! Generated-side interface for the hand-extracted VCs. This imports no proof
provider. Byte offsets identify the invariant cutpoint and exit edge. -/

namespace VeriPyAsm.Examples.Triangular

open Verification

veripy_vcs obligations : VerifiedArtifact triangularArtifact triangularContract
    via Assembly.verified where
  init : VC.loop6.init at 6 vc_kind "initialization"
  preserve : VC.loop6.preserve at 6 vc_kind "preservation"
  exit : VC.loop6.exit at 58 vc_kind "normal_exit"
  decrease : VC.loop6.decrease at 6 vc_kind "ranking"

end VeriPyAsm.Examples.Triangular
