import VeriPyAsm.Examples.Bytecode
import VeriPyAsm.Verification.Artifact

/-! A universal contract proof for the imported scalar `add1` artifact.
The instruction bytes and their checked translation are reused from the literal
example; the input integer remains symbolic throughout the proof. The contract
describes integer inputs and normal/exceptional observations independently of
instruction offsets or a fixed fuel budget. -/

namespace VeriPyAsm.Examples

open Semantics Verification

def add1Admitted : StackAdmitted add1Artifact := admit_bytecode% add1Artifact

/-- Every integer input returns its successor after five decoded instructions.
The final PC is an execution detail, not part of the public functional contract. -/
theorem add1_run (n : Int) :
    run (step add1Admitted.translation.program) 5 { locals := [some (.int n)] } =
      .halted (.returned (.int (n + 1)) { pc := 18, locals := [some (.int n)] }) := by
  rfl

/-- Exact integers are accepted; Boolean inputs are deliberately outside this
contract even though the underlying Python operation also accepts them. -/
def add1Contract : Contract Int where
  pre n initial := initial = { locals := [some (.int n)] }
  post n initial value final :=
    value = .int (n + 1) ∧ final.locals = initial.locals ∧ final.stack = []
  raises _ _ _ _ := False

/-- For every integer input, the imported program terminates with its successor,
preserves the input local, leaves an empty stack, and has no allowed exception. -/
theorem add1_total : TotalCorrect (step add1Admitted.translation.program) add1Contract := by
  apply TotalCorrect.of_run
  intro n initial hpre
  change initial = { locals := [some (.int n)] } at hpre
  subst initial
  refine ⟨5, .returned (.int (n + 1)) { pc := 18, locals := [some (.int n)] },
    add1_run n, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

/-- The same contract is about the decoded raw artifact, not just the elaborated
program. The translation certificate supplies the representation equality. -/
theorem add1_artifact_total : ArtifactTotalCorrect add1Artifact add1Contract :=
  add1Admitted.translation.artifact_total_iff.mpr add1_total

theorem add1_no_exception (n : Int) (fuel : Nat) (exception : PythonException)
    (failureFrame : Frame) :
    run (step add1Admitted.translation.program) fuel { locals := [some (.int n)] } ≠
      .halted (.raised exception failureFrame) := by
  intro execution
  exact add1_total.partialCorrect.run_halted (ghost := n) rfl execution

theorem add1_no_fault (n : Int) (fuel : Nat) (reason : Fault) (failureFrame : Frame) :
    run (step add1Admitted.translation.program) fuel { locals := [some (.int n)] } ≠
      .halted (.fault reason failureFrame) := by
  intro execution
  exact add1_total.partialCorrect.run_halted (ghost := n) rfl execution

end VeriPyAsm.Examples
