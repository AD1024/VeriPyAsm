import VeriPyAsm.Examples.Triangular.Assembly
import VeriPyAsm.Examples.Triangular.Arithmetic

/-! Public total-correctness theorems, obtained by supplying the ordinary Lean
proofs of the named VCs to the provider-independent assembly theorem. -/

namespace VeriPyAsm.Examples

open Semantics Verification
open scoped VeriPyAsm.Verification.Hoare

namespace Triangular

theorem loop_total (N : Int) :
    BlockTotalCorrect (step triangular.translation.program) (fun pc => pc = 58)
      (invariant N) { continues := exitInvariant N } :=
  Assembly.loop_total Arithmetic.proofs N

theorem finish_total (N : Int) :
    BlockTotalCorrect (step triangular.translation.program) (fun _ => False)
      (exitInvariant N) (postcondition N) :=
  Assembly.finish_total N

theorem program_total (N : Int) (nonnegative : 0 ≤ N) :
    BlockTotalCorrect (step triangular.translation.program) (fun _ => False)
      (fun initial => initial = { locals := [some (.int N), none] }) (postcondition N) :=
  Assembly.program_total Arithmetic.proofs N nonnegative

end Triangular

theorem triangular_total (N : Int) :
    {{ fun initial => 0 ≤ N ∧ initial = { locals := [some (.int N), none] } }}
      triangular.translation.program
    {{ returns fun value final => ∃ result : Int,
      value = .int result ∧ 2 * result = N * (N + 1) ∧
      final.locals = [some (.int 0), some (.int result)] ∧ final.stack = [] }} :=
  Triangular.Assembly.total Triangular.Arithmetic.proofs N

theorem triangular_contract_total :
    TotalCorrect (step triangular.translation.program) triangularContract :=
  Triangular.Assembly.contract_total Triangular.Arithmetic.proofs

theorem triangular_artifact_total : ArtifactTotalCorrect triangularArtifact triangularContract :=
  Triangular.Assembly.artifact_total Triangular.Arithmetic.proofs

def triangular_verified : VerifiedArtifact triangularArtifact triangularContract :=
  Triangular.Assembly.verified Triangular.Arithmetic.proofs

theorem triangular_no_exception (N : Int) (nonnegative : 0 ≤ N) (fuel : Nat)
    (exception : PythonException) (failureFrame : Frame) :
    run (step triangular.translation.program) fuel { locals := [some (.int N), none] } ≠
      .halted (.raised exception failureFrame) := by
  intro execution
  exact (triangular_total N).partialCorrect.run_halted (ghost := ()) ⟨nonnegative, rfl⟩ execution

theorem triangular_no_fault (N : Int) (nonnegative : 0 ≤ N) (fuel : Nat)
    (reason : Fault) (failureFrame : Frame) :
    run (step triangular.translation.program) fuel { locals := [some (.int N), none] } ≠
      .halted (.fault reason failureFrame) := by
  intro execution
  exact (triangular_total N).partialCorrect.run_halted (ghost := ()) ⟨nonnegative, rfl⟩ execution

end VeriPyAsm.Examples
