import VeriPyAsm.Examples.Add1

/-! Contract-boundary regressions. These distinguish divergence from termination,
Python exceptions from VM faults, and a proof about one raw artifact from a
freshly admitted mutation with different behavior. -/

namespace VeriPyAsm.Tests.Contracts

open Semantics Verification Examples CPython.V314

private def impossibleExits : Contract Unit where
  pre _ _ := True
  post _ _ _ _ := False
  raises _ _ _ _ := False

private def permissive : Contract Unit where
  pre _ _ := True
  post _ _ _ _ := True
  raises _ _ _ _ := True

private def selfLoop : Frame → StepResult := fun initial => .next initial

private theorem selfLoop_no_execution {initial : Frame} {outcome : Halt}
    (execution : Executes selfLoop initial outcome) : False := by
  induction execution with
  | halt transition => cases transition
  | step _ _ ih => exact ih

theorem divergence_partial : PartialCorrect selfLoop impossibleExits := by
  intro _ _ _ _ execution
  exact False.elim (selfLoop_no_execution execution)

theorem divergence_not_total : ¬ TotalCorrect selfLoop impossibleExits := by
  intro correct
  obtain ⟨_, execution⟩ := correct.terminates () {} trivial
  exact selfLoop_no_execution execution

-- Even every finite fuel bound being exhausted does not establish termination.
example (fuel : Nat) (initial : Frame) :
    run selfLoop fuel initial = .exhausted initial := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

private def immediateFault : Frame → StepResult := fun initial =>
  .halted (.fault (.invalidPC initial.pc) initial)

-- Neither user postcondition can legalize an internal VM fault.
theorem immediate_fault_rejected : ¬ PartialCorrect immediateFault permissive := by
  intro correct
  exact correct.no_fault (ghost := ()) (initial := {}) trivial (.invalidPC 0) {}
    (.halt rfl)

private def delayedFault : Frame → StepResult := fun initial =>
  if initial.pc = 0 then .next { initial with pc := 1 }
  else .halted (.fault (.invalidPC initial.pc) initial)

-- Checking only the initial transition would miss this faulting continuation.
theorem reachable_fault_rejected : ¬ PartialCorrect delayedFault permissive := by
  intro correct
  have path : Reaches delayedFault {} { pc := 1 } :=
    Reaches.of_run (fuel := 1) rfl
  exact correct.reachable_no_fault (ghost := ()) trivial path (.invalidPC 1)
    { pc := 1 } rfl

private def raisesTypeError : Frame → StepResult := fun initial =>
  .halted (.raised .typeError initial)

private def exceptionalContract : Contract Unit where
  pre _ _ := True
  post _ _ _ _ := False
  raises _ initial exception final := exception = .typeError ∧ final = initial

theorem allowed_exception_total : TotalCorrect raisesTypeError exceptionalContract := by
  apply TotalCorrect.of_run
  intro _ initial _
  exact ⟨1, .raised .typeError initial, rfl, rfl, rfl⟩

theorem forbidden_exception_rejected : ¬ PartialCorrect raisesTypeError impossibleExits := by
  intro correct
  exact correct () {} trivial (.raised .typeError {}) (.halt rfl)

-- Total correctness permits an explicitly specified exception, but does not
-- reinterpret it as a normal return.
example (initial final : Frame) (value : Value) :
    ¬ Executes raisesTypeError initial (.returned value final) := by
  intro execution
  have expected : Executes raisesTypeError initial (.raised .typeError initial) := .halt rfl
  cases expected.deterministic execution

example : ¬ exceptionalContract.Accepts () {} (.returned .none {}) := by
  intro allowed
  exact allowed

-- Zero fuel says nothing about whether the next transition returns or raises.
example (initial : Frame) : run raisesTypeError 0 initial = .exhausted initial := rfl

-- Reachability contains only continuing steps; an exception cannot resume.
example {initial current : Frame} (path : Reaches raisesTypeError initial current) :
    initial = current := by
  cases path with
  | refl => rfl
  | step transition _ => cases transition

example (n : Int) (extra : Nat) :
    run (step add1Admitted.translation.program) (5 + extra)
        { locals := [some (.int n)] } =
      .halted (.returned (.int (n + 1)) { pc := 18, locals := [some (.int n)] }) :=
  run_halted_add (add1_run n) extra

-- This function uses LOAD_SMALL_INT, so the effective constant is byte 5,
-- rather than the unused constant-table entry. The new program still admits.
def changedAdd1Artifact : Artifact :=
  { add1Artifact with code := add1Artifact.code.set 5 2 }

def changedAdd1 : StackAdmitted changedAdd1Artifact := admit_bytecode% changedAdd1Artifact

private theorem changedAdd1_run_zero :
    run (step changedAdd1.translation.program) 5 { locals := [some (.int 0)] } =
      .halted (.returned (.int 2) { pc := 18, locals := [some (.int 0)] }) := by
  rfl

theorem mutation_not_partial : ¬ ArtifactPartialCorrect changedAdd1Artifact add1Contract := by
  intro correct
  have shallow := changedAdd1.translation.artifact_partial_iff.mp correct
  have allowed := shallow.run_halted (ghost := 0) rfl changedAdd1_run_zero
  have wrong : (2 : Int) = 1 := Value.int.inj allowed.1
  exact (by decide : ¬ ((2 : Int) = 1)) wrong

theorem mutation_not_total : ¬ ArtifactTotalCorrect changedAdd1Artifact add1Contract :=
  fun correct => mutation_not_partial correct.to_partial

#print axioms divergence_partial
#print axioms divergence_not_total
#print axioms executes_iff_run
#print axioms reaches_iff_run_exhausted
#print axioms Executes.deterministic
#print axioms TotalCorrect.of_run
#print axioms reachable_fault_rejected
#print axioms allowed_exception_total
#print axioms mutation_not_total
#print axioms add1_artifact_total

end VeriPyAsm.Tests.Contracts
