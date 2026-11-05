import VeriPyAsm.Semantics.Block
import VeriPyAsm.Verification.Contract

/-! Compositional contracts for blocks of the existing deterministic machine.
Postconditions distinguish continuation, normal return, and Python exception.
Unspecified exits and all VM faults are forbidden. Cutpoints are observed before
executing their instruction. Termination of a block means reaching such a
cutpoint or an allowed halt, not necessarily returning from the whole program.

These are semantic rules, with no VC generator or solver dependency. Outer Lean
binders retain ghost values and initial frames for relational specifications. -/

namespace VeriPyAsm.Verification

open Semantics

structure Postcondition where
  continues : Frame → Prop := fun _ => False
  returns : Value → Frame → Prop := fun _ _ => False
  raises : PythonException → Frame → Prop := fun _ _ => False

def Postcondition.Accepts (post : Postcondition) : StepResult → Prop
  | .next frame => post.continues frame
  | .halted (.returned value frame) => post.returns value frame
  | .halted (.raised exception frame) => post.raises exception frame
  | .halted (.fault _ _) => False

/-- Close a block interface into a whole-program contract. Continuation is not
a whole-program outcome; the soundness rules below require an empty exit set. -/
def Postcondition.toContract (post : Postcondition) (pre : Frame → Prop) : Contract Unit where
  pre _ := pre
  post _ _ := post.returns
  raises _ _ := post.raises

def BlockPartialCorrect (next : Frame → StepResult) (exits : Nat → Prop)
    (pre : Frame → Prop) (post : Postcondition) : Prop :=
  ∀ initial, pre initial → ∀ result,
    BlockExecutes next exits initial result → post.Accepts result

structure BlockTotalCorrect (next : Frame → StepResult) (exits : Nat → Prop)
    (pre : Frame → Prop) (post : Postcondition) : Prop where
  partialCorrect : BlockPartialCorrect next exits pre post
  terminates : ∀ initial, pre initial → ∃ result, BlockExecutes next exits initial result

variable {next : Frame → StepResult} {exits cuts : Nat → Prop}
    {P P' R : Frame → Prop} {Q Q' : Postcondition}

theorem BlockTotalCorrect.of_execution
    (execute : ∀ initial, P initial →
      ∃ result, BlockExecutes next exits initial result ∧ Q.Accepts result) :
    BlockTotalCorrect next exits P Q := by
  constructor
  · intro initial pre result execution
    obtain ⟨expected, observed, allowed⟩ := execute initial pre
    have equal := observed.deterministic execution
    cases equal
    exact allowed
  · intro initial pre
    obtain ⟨result, execution, _⟩ := execute initial pre
    exact ⟨result, execution⟩

theorem BlockPartialCorrect.consequence (correct : BlockPartialCorrect next exits P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ result, Q.Accepts result → Q'.Accepts result) :
    BlockPartialCorrect next exits P' Q' :=
  fun s h result execution => post result (correct s (pre s h) result execution)

theorem BlockTotalCorrect.consequence (correct : BlockTotalCorrect next exits P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ result, Q.Accepts result → Q'.Accepts result) :
    BlockTotalCorrect next exits P' Q' :=
  ⟨correct.partialCorrect.consequence pre post, fun s h => correct.terminates s (pre s h)⟩

/-- Zero steps suffice at a designated exit. No instruction there is executed. -/
theorem BlockTotalCorrect.exit (atExit : ∀ s, P s → exits s.pc)
    (post : ∀ s, P s → Q.continues s) : BlockTotalCorrect next exits P Q := by
  apply BlockTotalCorrect.of_execution
  intro s pre
  exact ⟨.next s, .exit (atExit s pre), post s pre⟩

/-- Sequence blocks through the assertion R. Both blocks share their return and
exception postconditions: only a continuing exit invokes the suffix. Include
all final exits among the prefix cutpoints (typically `cuts = R-labels ∪ exits`). -/
theorem BlockPartialCorrect.seq
    (first : BlockPartialCorrect next cuts P { Q with continues := R })
    (suffix : BlockPartialCorrect next exits R Q)
    (contains : ∀ pc, exits pc → cuts pc) : BlockPartialCorrect next exits P Q := by
  intro initial pre result execution
  obtain ⟨middle, before, after⟩ := execution.split contains
  have allowed := first initial pre middle before
  cases middle with
  | next frame => exact suffix frame allowed result after
  | halted outcome =>
    cases after
    cases outcome <;> exact allowed

theorem BlockTotalCorrect.seq
    (first : BlockTotalCorrect next cuts P { Q with continues := R })
    (suffix : BlockTotalCorrect next exits R Q)
    (contains : ∀ pc, exits pc → cuts pc) : BlockTotalCorrect next exits P Q := by
  apply BlockTotalCorrect.of_execution
  intro initial pre
  obtain ⟨middle, before⟩ := first.terminates initial pre
  have allowed := first.partialCorrect initial pre middle before
  cases middle with
  | next frame =>
    obtain ⟨result, after⟩ := suffix.terminates frame allowed
    exact ⟨result, before.append contains after, suffix.partialCorrect frame allowed result after⟩
  | halted outcome =>
    refine ⟨.halted outcome, before.append contains rfl, ?_⟩
    cases outcome <;> exact allowed

/-- With no continuation exits, the block judgment entails the original
whole-program partial-correctness contract, including exclusion of faults. -/
theorem BlockPartialCorrect.to_partialCorrect
    (correct : BlockPartialCorrect next (fun _ => False) P Q) :
    PartialCorrect next (Q.toContract P) := by
  intro _ initial pre outcome execution
  have allowed := correct initial pre (.halted outcome) (.of_execution execution)
  cases outcome <;> exact allowed

theorem BlockTotalCorrect.to_totalCorrect
    (correct : BlockTotalCorrect next (fun _ => False) P Q) :
    TotalCorrect next (Q.toContract P) := by
  refine ⟨correct.partialCorrect.to_partialCorrect, ?_⟩
  intro _ initial pre
  obtain ⟨result, execution⟩ := correct.terminates initial pre
  cases result with
  | next frame => exact False.elim execution.exit_at
  | halted outcome => exact ⟨outcome, execution.halts⟩

end VeriPyAsm.Verification
