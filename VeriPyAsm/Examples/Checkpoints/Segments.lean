import VeriPyAsm.Examples.Checkpoints.VC
import VeriPyAsm.Examples.Assertions.Generated

/-! Reusable semantic proofs of the assertion and return segments. No proof
registrations or arithmetic-hint provider are imported. -/

set_option maxHeartbeats 2000000

namespace VeriPyAsm.Examples.Checkpoints.Segments

open Semantics Verification

private theorem dispatch {program : Program} {current : Frame} {command : Command}
    (lookup : program current.pc = some command) : step program current = command current := by
  simp only [step, lookup]

theorem entry : VC.entry := by
  rintro n initial ⟨_, rfl⟩
  exact ⟨rfl, rfl, [.int n], rfl, rfl⟩

theorem runtimeAssertion : VC.runtimeAssertion := by
  intro n nonnegative
  change Verification.VC.wp (step Assertions.nonnegative.translation.program) [20]
    { post n with continues := context n } 6
    { pc := 10, locals := [some (.int n)], stack := [.bool (decide (0 ≤ n))] }
  rw [show decide (0 ≤ n) = true from decide_eq_true nonnegative]
  exact ⟨rfl, nonnegative⟩

theorem finish : VC.finish := by
  rintro n current ⟨⟨rfl, _⟩, established⟩
  -- Reuse checked dispatch equations for these exact bytes. Avoid repeatedly
  -- unfolding the decoder through the admission certificate during reduction.
  have loaded : step Assertions.ExceptionFree.generated.program
      { pc := 20, locals := [some (.int n)] } =
      .next { pc := 22, locals := [some (.int n)], stack := [.int n] } :=
    dispatch (program := Assertions.ExceptionFree.generated.program)
      (current := { pc := 20, locals := [some (.int n)] })
      (command := Command.load false 22 0) Assertions.ExceptionFree.generated.lookup_20
  have returned : step Assertions.ExceptionFree.generated.program
      { pc := 22, locals := [some (.int n)], stack := [.int n] } =
      .halted (.returned (.int n) { pc := 22, locals := [some (.int n)] }) :=
    dispatch (program := Assertions.ExceptionFree.generated.program)
      (current := { pc := 22, locals := [some (.int n)], stack := [.int n] })
      (command := Command.ret) Assertions.ExceptionFree.generated.lookup_22
  rw [← Assertions.ExceptionFree.generated.representation]
  exact Verification.VC.wp_of_next rfl loaded
    (Verification.VC.wp_of_halt rfl returned ⟨rfl, established, rfl, rfl⟩)


#veripy_audit VeriPyAsm.Examples.Checkpoints.Segments

end VeriPyAsm.Examples.Checkpoints.Segments
