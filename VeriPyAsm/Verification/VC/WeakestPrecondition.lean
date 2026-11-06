import VeriPyAsm.Verification.Loop
import VeriPyAsm.Verification.VerifiedArtifact

/-! Finite symbolic execution between annotated cutpoints. Fuel bounds a single
acyclic segment, never the whole execution. Exhaustion outside a cutpoint is
False; faults are always False. Crossing a cutpoint starts with a real step, so
neither an invariant nor a ranking can justify a zero-step loop.

The generator only chooses segment bounds and simplifies these propositions.
These semantic rules and the kernel-checked simplification certificates carry
the soundness argument, independently of the control-flow analysis or solver.
-/

namespace VeriPyAsm.Verification.VC

open Semantics

/-- Native predicates retain both ghosts and the original call frame. A single
invariant can distinguish several cutpoints by `current.pc`. A total run uses
one natural ranking across all cutpoint transitions. -/
structure Specification (Ghost : Type) where
  contract : Contract Ghost
  mode : CorrectnessMode := .totalCorrectness
  cutpoints : List Nat := []
  invariant : Ghost → Frame → Frame → Prop := fun _ _ _ => False
  ranking : Option (Ghost → Frame → Frame → Nat) := none

def wp (next : Frame → StepResult) (cuts : List Nat) (post : Postcondition) :
    Nat → Frame → Prop
  | 0, s => cuts.contains s.pc = true ∧ post.continues s
  | fuel + 1, s =>
    if cuts.contains s.pc then post.continues s
    else match next s with
      | .next current => wp next cuts post fuel current
      | .halted outcome => post.Accepts (.halted outcome)

def iterationWP (next : Frame → StepResult) (cuts : List Nat)
    (post : Postcondition) (fuel : Nat) (s : Frame) : Prop :=
  match next s with
  | .next current => wp next cuts post fuel current
  | .halted outcome => post.Accepts (.halted outcome)

/-- Expose the branch outside the frame before symbolic dispatch. Both targets
then retain literal PCs, instead of expanding lookup at an unknown `if` label. -/
theorem branch_split (ifTrue ifFalse : Nat) (s : Frame) :
    Command.branch ifTrue ifFalse s =
      match s.stack with
      | .bool b :: rest =>
        if b then .next { s with pc := ifTrue, stack := rest }
        else .next { s with pc := ifFalse, stack := rest }
      | [] => .halted (.fault .stackUnderflow s)
      | _ => .halted (.fault .expectedBool s) := by
  cases s with
  | mk pc locals stack =>
    cases stack with
    | nil => rfl
    | cons value rest =>
      cases value with
      | int n => rfl
      | none => rfl
      | assertionErrorType => rfl
      | bool b => cases b <;> rfl

theorem wp_execution {next : Frame → StepResult} {cuts : List Nat}
    {post : Postcondition} {fuel : Nat} {s : Frame}
    (valid : wp next cuts post fuel s) :
    ∃ result, BlockExecutes next (fun pc => cuts.contains pc = true) s result ∧
      post.Accepts result := by
  induction fuel generalizing s with
  | zero => exact ⟨.next s, .exit valid.1, valid.2⟩
  | succ fuel ih =>
    by_cases atCut : cuts.contains s.pc = true
    · exact ⟨.next s, .exit atCut, by
        change post.continues s
        simpa only [wp, atCut, ↓reduceIte] using valid⟩
    · simp only [wp, atCut] at valid
      cases transition : next s with
      | next current =>
        rw [transition] at valid
        obtain ⟨result, execution, allowed⟩ := ih valid
        exact ⟨result, .step atCut transition execution, allowed⟩
      | halted outcome =>
        rw [transition] at valid
        exact ⟨.halted outcome, .halt atCut transition, valid⟩

theorem wp_total {next : Frame → StepResult} {cuts : List Nat}
    {post : Postcondition} {fuel : Nat} {pre : Frame → Prop}
    (valid : ∀ s, pre s → wp next cuts post fuel s) :
    BlockTotalCorrect next (fun pc => cuts.contains pc = true) pre post :=
  .of_execution fun s h => wp_execution (valid s h)

theorem iterationWP_total {next : Frame → StepResult} {cuts : List Nat}
    {post : Postcondition} {fuel : Nat} {pre : Frame → Prop}
    (valid : ∀ s, pre s → iterationWP next cuts post fuel s) :
    IterationTotalCorrect next (fun pc => cuts.contains pc = true) pre post := by
  apply IterationTotalCorrect.of_execution
  intro s pre
  have allowed := valid s pre
  cases transition : next s with
  | next current =>
    simp only [iterationWP, transition] at allowed
    obtain ⟨result, execution, post⟩ := wp_execution allowed
    exact ⟨result, .step transition execution, post⟩
  | halted outcome =>
    exact ⟨.halted outcome, .halt transition, by
      simpa only [iterationWP, transition] using allowed⟩

namespace Specification

variable {Ghost : Type}

def atCut (spec : Specification Ghost) (ghost : Ghost) (initial current : Frame) : Prop :=
  spec.cutpoints.contains current.pc = true ∧ spec.invariant ghost initial current

def post (spec : Specification Ghost) (ghost : Ghost) (initial : Frame) : Postcondition where
  returned := spec.contract.post ghost initial
  raises := spec.contract.raises ghost initial

def rank (spec : Specification Ghost) (ghost : Ghost) (initial current : Frame) : Nat :=
  (spec.ranking.getD (fun _ _ _ => 0)) ghost initial current

def entryPost (spec : Specification Ghost) (ghost : Ghost) (initial : Frame) : Postcondition :=
  { spec.post ghost initial with continues := spec.atCut ghost initial }

def bodyPost (spec : Specification Ghost) (ghost : Ghost) (initial old : Frame) : Postcondition :=
  { spec.post ghost initial with
    continues := fun current =>
      spec.atCut ghost initial current ∧ (match spec.mode with
        | .partialCorrectness => True
        | .totalCorrectness => spec.rank ghost initial current < spec.rank ghost initial old) }

def EntryVC (artifact : CPython.V314.Artifact) (spec : Specification Ghost) : Prop :=
  ∀ ghost initial, spec.contract.pre ghost initial → EntryFrame artifact initial

def InitVC (next : Frame → StepResult) (spec : Specification Ghost) (fuel : Nat) : Prop :=
  ∀ ghost initial, spec.contract.pre ghost initial →
    wp next spec.cutpoints (spec.entryPost ghost initial) fuel initial

def BodyVC (next : Frame → StepResult) (spec : Specification Ghost)
    (fuel pc : Nat) : Prop :=
  ∀ ghost initial, spec.contract.pre ghost initial →
    ∀ current, current.pc = pc → spec.invariant ghost initial current →
      iterationWP next spec.cutpoints (spec.bodyPost ghost initial current) fuel current

/-- A transparent conjunction lets the generator assemble separately named VCs
without relying on proof search to cover the complete cutpoint list. -/
def BodiesVC (next : Frame → StepResult) (spec : Specification Ghost) (fuel : Nat) :
    List Nat → Prop
  | [] => True
  | pc :: rest => spec.BodyVC next fuel pc ∧ spec.BodiesVC next fuel rest

theorem BodiesVC.member {next : Frame → StepResult} {spec : Specification Ghost}
    {fuel pc : Nat} {pcs : List Nat} (valid : spec.BodiesVC next fuel pcs)
    (member : pc ∈ pcs) : spec.BodyVC next fuel pc := by
  induction pcs with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact valid.1
    · exact ih valid.2 member

private theorem body {next : Frame → StepResult} {spec : Specification Ghost}
    {fuel : Nat} (valid : spec.BodiesVC next fuel spec.cutpoints)
    {ghost : Ghost} {initial : Frame} (pre : spec.contract.pre ghost initial)
    {current : Frame} (invariant : spec.atCut ghost initial current) :
    IterationTotalCorrect next (fun pc => spec.cutpoints.contains pc = true)
      (fun s => s = current) (spec.bodyPost ghost initial current) := by
  apply iterationWP_total
  intro s equal
  subst s
  exact valid.member (List.contains_iff_mem.mp invariant.1) ghost initial pre
    current rfl invariant.2

theorem partialCorrect {next : Frame → StepResult} {spec : Specification Ghost}
    {fuel : Nat} (entry : spec.InitVC next fuel)
    (bodies : spec.BodiesVC next fuel spec.cutpoints) : PartialCorrect next spec.contract := by
  intro ghost initial pre outcome execution
  have first : BlockTotalCorrect next (fun pc => spec.cutpoints.contains pc = true)
      (fun s => s = initial) (spec.entryPost ghost initial) :=
    wp_total (by intro s equal; subst s; exact entry ghost initial pre)
  have loop : BlockPartialCorrect next (fun _ => False)
      (spec.atCut ghost initial) (spec.post ghost initial) := by
    apply BlockPartialCorrect.loop (cuts := fun pc => spec.cutpoints.contains pc = true)
      (fun _ h => h.elim) (fun _ _ h => h)
    intro current invariant result iteration
    have allowed := (body bodies pre invariant).partialCorrect current rfl result iteration
    cases result with
    | next frame => exact Or.inr allowed.1
    | halted halt => cases halt <;> exact allowed
  have allowed := (first.partialCorrect.seq loop (fun _ h => h.elim))
    initial rfl (.halted outcome) (.of_execution execution)
  cases outcome <;> exact allowed

theorem totalCorrect {next : Frame → StepResult} {spec : Specification Ghost}
    {fuel : Nat} (mode : spec.mode = .totalCorrectness) (entry : spec.InitVC next fuel)
    (bodies : spec.BodiesVC next fuel spec.cutpoints) : TotalCorrect next spec.contract := by
  apply TotalCorrect.of_execution
  intro ghost initial pre
  have first : BlockTotalCorrect next (fun pc => spec.cutpoints.contains pc = true)
      (fun s => s = initial) (spec.entryPost ghost initial) :=
    wp_total (by intro s equal; subst s; exact entry ghost initial pre)
  have loop : BlockTotalCorrect next (fun _ => False)
      (spec.atCut ghost initial) (spec.post ghost initial) := by
    apply BlockTotalCorrect.loop (cuts := fun pc => spec.cutpoints.contains pc = true)
      (spec.rank ghost initial) (fun _ h => h.elim) (fun _ _ h => h)
    intro current invariant
    apply (body bodies pre invariant).consequence (fun _ h => h)
    intro result allowed
    cases result with
    | next frame =>
      apply Or.inr
      simpa only [bodyPost, Postcondition.Accepts, mode] using allowed
    | halted halt => cases halt <;> exact allowed
  obtain ⟨result, execution⟩ := (first.seq loop (fun _ h => h.elim)).terminates initial rfl
  have allowed := (first.seq loop (fun _ h => h.elim)).partialCorrect initial rfl result execution
  cases result with
  | next frame => exact False.elim execution.exit_at
  | halted outcome =>
    refine ⟨outcome, execution.halts, ?_⟩
    cases outcome <;> exact allowed

def verified {Ghost : Type} {artifact : CPython.V314.Artifact}
    (admission : Admitted artifact) (spec : Specification Ghost) (fuel : Nat)
    (program : Program) (representation : step program = step admission.translation.program)
    (entry : spec.EntryVC artifact) (init : spec.InitVC (step program) fuel)
    (bodies : spec.BodiesVC (step program) fuel spec.cutpoints) :
    VerifiedArtifact artifact spec.contract spec.mode where
  admission := admission
  entry := entry
  correctness := by
    rw [← representation]
    cases mode : spec.mode with
    | partialCorrectness => exact partialCorrect init bodies
    | totalCorrectness => exact totalCorrect mode init bodies

end Specification
end VeriPyAsm.Verification.VC
