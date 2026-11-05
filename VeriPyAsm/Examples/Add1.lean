import VeriPyAsm.Examples.Bytecode
import VeriPyAsm.Verification.VerifiedArtifact
import VeriPyAsm.Verification.AxiomAudit
import VeriPyAsm.Verification.Hoare
import VeriPyAsm.Verification.Instruction

/-! A universal contract proof for the imported scalar `add1` artifact.
The instruction bytes and their checked translation are reused from the literal
example; the input integer remains symbolic throughout the proof. The contract
describes integer inputs and normal/exceptional observations independently of
instruction offsets or a fixed fuel budget. -/

namespace VeriPyAsm.Examples

open Semantics Verification
open scoped VeriPyAsm.Verification.Hoare

def add1Admitted : Admitted add1Artifact := admit_bytecode% add1Artifact

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
theorem add1_total (n : Int) :
    {{ fun initial => initial = { locals := [some (.int n)] } }}
      add1Admitted.translation.program
    {{ returns fun value final =>
      value = .int (n + 1) ∧ final.locals = [some (.int n)] ∧ final.stack = [] }} := by
  let state (pc : Nat) (stack : List Value) : Frame :=
    { pc, locals := [some (.int n)], stack }
  let post : Postcondition :=
    { returned := fun value final =>
        value = .int (n + 1) ∧ final.locals = [some (.int n)] ∧ final.stack = [] }

  -- RETURN_VALUE at 18: pop the ordinary result and close the block.
  have returnRule := (InstructionCorrect.ret post).on_frame
    (initial := state 18 [.int (n + 1)]) ⟨.int (n + 1), [], rfl, rfl, rfl, rfl⟩
  have returned : BlockTotalCorrect (step add1Admitted.translation.program) (fun _ => False)
      (fun s => s = state 18 [.int (n + 1)]) post :=
    returnRule.to_block (by rintro s rfl; rfl) (fun _ _ h => h) (fun _ h => h)

  -- BINARY_OP + at 6: its inline caches end at offset 18.
  have addRule := (InstructionCorrect.binary 18 (Semantics.binary .add)
    { post with continues := fun s => s = state 18 [.int (n + 1)] }).on_frame
    (initial := state 6 [.int 1, .int n])
    ⟨.int n, .int 1, [], .int (n + 1), rfl, rfl, rfl⟩
  have added := addRule.prepend
    (by rintro s rfl; rfl) (fun _ _ h => h) returned

  have pushRule := (InstructionCorrect.push 6 (.int 1)
    { post with continues := fun s => s = state 6 [.int 1, .int n] }).on_frame
    (initial := state 4 [.int n]) rfl
  have pushed := pushRule.prepend
    (by rintro s rfl; rfl) (fun _ _ h => h) added

  have loadRule := (InstructionCorrect.load false 4 0
    { post with continues := fun s => s = state 4 [.int n] }).on_frame
    (initial := state 2 []) ⟨.int n, rfl, rfl⟩
  have loaded := loadRule.prepend
    (by rintro s rfl; rfl) (fun _ _ h => h) pushed

  -- RESUME at 0 is the scalar profile's jump to the next instruction.
  have resumeRule := (InstructionCorrect.jump 2
    { post with continues := fun s => s = state 2 [] }).on_frame
    (initial := state 0 []) rfl
  exact (resumeRule.prepend
    (by rintro s rfl; rfl) (fun _ _ h => h) loaded).to_totalCorrect

/-- Package the notation-based theorem in the original relational contract.
The entry precondition identifies the local preserved by the postcondition. -/
theorem add1_contract_total :
    TotalCorrect (step add1Admitted.translation.program) add1Contract := by
  apply TotalCorrect.of_execution
  intro n initial hpre
  change initial = { locals := [some (.int n)] } at hpre
  subst initial
  obtain ⟨outcome, execution⟩ :=
    (add1_total n).terminates () { locals := [some (.int n)] } rfl
  exact ⟨outcome, execution,
    (add1_total n).partialCorrect () { locals := [some (.int n)] } rfl outcome execution⟩

/-- The same contract is about the decoded raw artifact, not just the elaborated
program. The translation certificate supplies the representation equality. -/
theorem add1_artifact_total : ArtifactTotalCorrect add1Artifact add1Contract :=
  add1Admitted.translation.artifact_total_iff.mpr add1_contract_total

/-- Final package: both admission certificates, call-entry compatibility, and
total correctness of the same certified translation. -/
def add1_verified : VerifiedArtifact add1Artifact add1Contract where
  admission := add1Admitted
  entry := by
    rintro n initial rfl
    exact ⟨rfl, rfl, [.int n], rfl, rfl⟩
  correctness := add1_contract_total

theorem add1_no_exception (n : Int) (fuel : Nat) (exception : PythonException)
    (failureFrame : Frame) :
    run (step add1Admitted.translation.program) fuel { locals := [some (.int n)] } ≠
      .halted (.raised exception failureFrame) := by
  intro execution
  exact (add1_total n).partialCorrect.run_halted (ghost := ()) rfl execution

theorem add1_no_fault (n : Int) (fuel : Nat) (reason : Fault) (failureFrame : Frame) :
    run (step add1Admitted.translation.program) fuel { locals := [some (.int n)] } ≠
      .halted (.fault reason failureFrame) := by
  intro execution
  exact (add1_total n).partialCorrect.run_halted (ghost := ()) rfl execution

end VeriPyAsm.Examples

#veripy_audit VeriPyAsm.Examples
