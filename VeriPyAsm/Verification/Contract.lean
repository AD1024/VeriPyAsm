import VeriPyAsm.Semantics.Execution

/-! Relational contracts for the deterministic, sequential scalar machine.
Ghost parameters retain logical inputs without becoming machine state. Normal
and exceptional postconditions can observe both the initial and terminal frames.

Partial correctness permits divergence but never a VM fault. Total correctness
adds finite termination for every initial frame satisfying the precondition.
Stack capacity and artifact metadata are separate admission properties. -/

namespace VeriPyAsm.Verification

open Semantics

universe u

structure Contract (Ghost : Type u) where
  pre : Ghost → Frame → Prop
  post : Ghost → Frame → Value → Frame → Prop
  raises : Ghost → Frame → PythonException → Frame → Prop

/-- VM faults cannot be allowed by weakening either user postcondition. -/
def Contract.Accepts {Ghost : Type u} (contract : Contract Ghost)
    (ghost : Ghost) (initial : Frame) : Halt → Prop
  | .returned value final => contract.post ghost initial value final
  | .raised exception final => contract.raises ghost initial exception final
  | .fault _ _ => False

def PartialCorrect {Ghost : Type u} (next : Frame → StepResult)
    (contract : Contract Ghost) : Prop :=
  ∀ ghost initial, contract.pre ghost initial →
    ∀ outcome, Executes next initial outcome → contract.Accepts ghost initial outcome

/-- Existence of a finite execution expresses termination here because `next`
is deterministic. This is not a termination rule for nondeterministic schedules. -/
structure TotalCorrect {Ghost : Type u} (next : Frame → StepResult)
    (contract : Contract Ghost) : Prop where
  partialCorrect : PartialCorrect next contract
  terminates : ∀ ghost initial, contract.pre ghost initial →
    ∃ outcome, Executes next initial outcome

variable {Ghost : Type u} {next : Frame → StepResult} {contract : Contract Ghost}

theorem PartialCorrect.run_halted (correct : PartialCorrect next contract)
    {ghost : Ghost} {initial : Frame} (pre : contract.pre ghost initial)
    {fuel : Nat} {outcome : Halt} (execution : run next fuel initial = .halted outcome) :
    contract.Accepts ghost initial outcome :=
  correct ghost initial pre outcome (Executes.of_run execution)

theorem PartialCorrect.no_fault (correct : PartialCorrect next contract)
    {ghost : Ghost} {initial : Frame} (pre : contract.pre ghost initial)
    (reason : Fault) (failureFrame : Frame) :
    ¬ Executes next initial (.fault reason failureFrame) :=
  fun execution => correct ghost initial pre _ execution

/-- Even a divergent execution cannot pass through a frame whose next step faults.
There is no vacuous success from omitting faulting executions from the relation. -/
theorem PartialCorrect.reachable_no_fault (correct : PartialCorrect next contract)
    {ghost : Ghost} {initial current : Frame} (pre : contract.pre ghost initial)
    (path : Reaches next initial current) (reason : Fault) (failureFrame : Frame) :
    next current ≠ .halted (.fault reason failureFrame) := by
  intro failure
  exact correct.no_fault pre reason failureFrame (path.executes (.halt failure))

/-- A symbolic allowed execution for every pre-state suffices for total correctness.
Outcome determinism supplies the universal partial-correctness component. -/
theorem TotalCorrect.of_execution
    (execute : ∀ ghost initial, contract.pre ghost initial →
      ∃ outcome, Executes next initial outcome ∧ contract.Accepts ghost initial outcome) :
    TotalCorrect next contract := by
  constructor
  · intro ghost initial pre outcome execution
    obtain ⟨expected, observed, allowed⟩ := execute ghost initial pre
    have equal := observed.deterministic execution
    cases equal
    exact allowed
  · intro ghost initial pre
    obtain ⟨outcome, execution, _⟩ := execute ghost initial pre
    exact ⟨outcome, execution⟩

/-- The fuel may depend on the ghost and initial frame. Quantification over all
pre-states distinguishes this rule from testing a finite collection of inputs. -/
theorem TotalCorrect.of_run
    (execute : ∀ ghost initial, contract.pre ghost initial →
      ∃ fuel outcome, run next fuel initial = .halted outcome ∧
        contract.Accepts ghost initial outcome) :
    TotalCorrect next contract := by
  apply TotalCorrect.of_execution
  intro ghost initial pre
  obtain ⟨_, outcome, execution, allowed⟩ := execute ghost initial pre
  exact ⟨outcome, Executes.of_run execution, allowed⟩

theorem TotalCorrect.exists_run (correct : TotalCorrect next contract)
    {ghost : Ghost} {initial : Frame} (pre : contract.pre ghost initial) :
    ∃ fuel outcome, run next fuel initial = .halted outcome ∧
      contract.Accepts ghost initial outcome := by
  obtain ⟨outcome, execution⟩ := correct.terminates ghost initial pre
  obtain ⟨fuel, observed⟩ := execution.to_run
  exact ⟨fuel, outcome, observed, correct.partialCorrect ghost initial pre outcome execution⟩

end VeriPyAsm.Verification
