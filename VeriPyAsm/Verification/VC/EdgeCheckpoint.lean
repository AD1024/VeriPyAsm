import VeriPyAsm.Verification.VC.WeakestPrecondition

/-! Checkpoint obligations are separate views of the same finite execution.
The main view checks safety, exits, and ranking while assuming checkpoint claims.
Each selected view must establish its own claims before using them downstream.
Combining every view recovers the ordinary WP, without changing the machine,
resetting fuel, or counting a logical claim as a loop step. -/

namespace VeriPyAsm.Verification.VC
open Semantics

structure EdgeCheckpoint (Ghost : Type) where
  label : String
  kind : String := "logical_checkpoint"
  edges : List (Nat × Nat)
  claim : (Frame → StepResult) → Ghost → Frame → Frame → Prop

structure CheckpointSpecification (Ghost : Type) where
  base : Specification Ghost
  checkpoints : List (EdgeCheckpoint Ghost)

namespace Checkpoint
variable {Ghost : Type}

/-- Actual assertion evaluation must reach a normal passing exit. This does not
interpret the source predicate or permit returns, exceptions, faults, or exhaustion. -/
def assertionPass (next : Frame → StepResult) (exits : List Nat) (fuel : Nat) (s : Frame) : Prop :=
  wp next exits { continues := fun _ => True } fuel s

def terminal {Label : Type} : Option Label → Prop → Prop
  | none, goal => goal
  | some _, _ => True

def guard {Label : Type} [DecidableEq Label] (selected : Option Label)
    (label : Label) (claim after : Prop) : Prop :=
  if selected = some label then claim ∧ (claim → after) else claim → after

private theorem guard_all {Label : Type} [DecidableEq Label] {label : Label}
    {claim : Prop} {after : Option Label → Prop}
    (valid : ∀ selected, guard selected label claim (after selected)) : ∀ selected, after selected := by
  have established : claim := (by simpa only [guard, ↓reduceIte] using valid (some label) :
    claim ∧ (claim → after (some label))).1
  intro selected
  have proof := valid selected
  unfold guard at proof
  split at proof
  · exact proof.2 established
  · exact proof established

/-- Preserve order when several hints share an edge. The incoming proof of a
claim has only earlier claims as premises, never itself or a later hint. -/
def edgeChecks (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (ghost : Ghost) (initial : Frame) (selected : Option (Fin checks.length))
    (before current : Frame) (after : Prop) : List (Fin checks.length) → Prop
  | [] => after
  | index :: rest =>
    let tail := edgeChecks next checks ghost initial selected before current after rest
    if checks[index].edges.contains (before.pc, current.pc) then
      guard selected index (checks[index].claim next ghost initial current) tail
    else tail

theorem edgeChecks_all {next : Frame → StepResult} {checks : List (EdgeCheckpoint Ghost)}
    {ghost : Ghost} {initial before current : Frame} {after : Option (Fin checks.length) → Prop}
    {indices : List (Fin checks.length)}
    (valid : ∀ selected, edgeChecks next checks ghost initial selected before current (after selected) indices) :
    ∀ selected, after selected := by
  induction indices with
  | nil => exact valid
  | cons index rest ih =>
    apply ih
    by_cases applies : checks[index].edges.contains (before.pc, current.pc) = true
    · refine guard_all (label := index) (claim := checks[index].claim next ghost initial current)
        (after := fun selected => edgeChecks next checks ghost initial selected before current (after selected) rest) ?_
      intro selected
      simpa only [edgeChecks, applies, ↓reduceIte] using valid selected
    · intro selected
      simpa only [edgeChecks, applies, Bool.false_eq_true, ↓reduceIte] using valid selected

def wp (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (ghost : Ghost) (initial : Frame) (selected : Option (Fin checks.length))
    (cuts : List Nat) (post : Postcondition) : Nat → Frame → Prop
  | 0, s => terminal selected (cuts.contains s.pc = true ∧ post.continues s)
  | fuel + 1, s =>
    if cuts.contains s.pc then terminal selected (post.continues s)
    else match next s with
      | .next current => edgeChecks next checks ghost initial selected s current
          (wp next checks ghost initial selected cuts post fuel current) (List.finRange checks.length)
      | .halted outcome => terminal selected (post.Accepts (.halted outcome))

def iterationWP (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (ghost : Ghost) (initial : Frame) (selected : Option (Fin checks.length))
    (cuts : List Nat) (post : Postcondition) (fuel : Nat) (s : Frame) : Prop :=
  match next s with
  | .next current => edgeChecks next checks ghost initial selected s current
      (wp next checks ghost initial selected cuts post fuel current) (List.finRange checks.length)
  | .halted outcome => terminal selected (post.Accepts (.halted outcome))

theorem wp_sound {next : Frame → StepResult} {checks : List (EdgeCheckpoint Ghost)}
    {ghost : Ghost} {initial s : Frame} {cuts : List Nat} {post : Postcondition} {fuel : Nat}
    (valid : ∀ selected, wp next checks ghost initial selected cuts post fuel s) :
    VC.wp next cuts post fuel s := by
  induction fuel generalizing s with
  | zero => exact valid none
  | succ fuel ih =>
    by_cases atCut : cuts.contains s.pc = true
    · simpa only [wp, VC.wp, atCut, ↓reduceIte, terminal] using valid none
    · simp only [VC.wp, atCut, Bool.false_eq_true, ↓reduceIte]
      cases transition : next s with
      | next current =>
        apply ih
        refine edgeChecks_all (next := next) (ghost := ghost) (initial := initial) (before := s)
          (current := current) (after := fun selected => wp next checks ghost initial selected cuts post fuel current)
          (indices := List.finRange checks.length) ?_
        intro selected
        simpa only [wp, atCut, Bool.false_eq_true, ↓reduceIte, transition] using valid selected
      | halted outcome =>
        simpa only [wp, atCut, Bool.false_eq_true, ↓reduceIte, transition, terminal] using valid none

theorem iterationWP_sound {next : Frame → StepResult} {checks : List (EdgeCheckpoint Ghost)}
    {ghost : Ghost} {initial s : Frame} {cuts : List Nat} {post : Postcondition} {fuel : Nat}
    (valid : ∀ selected, iterationWP next checks ghost initial selected cuts post fuel s) :
    VC.iterationWP next cuts post fuel s := by
  unfold VC.iterationWP
  cases transition : next s with
  | next current =>
    apply wp_sound (checks := checks) (ghost := ghost) (initial := initial)
    refine edgeChecks_all (next := next) (ghost := ghost) (initial := initial) (before := s)
      (current := current) (after := fun selected => wp next checks ghost initial selected cuts post fuel current)
      (indices := List.finRange checks.length) ?_
    intro selected
    simpa only [iterationWP, transition] using valid selected
  | halted outcome => simpa only [iterationWP, transition, terminal] using valid none

end Checkpoint

namespace CheckpointSpecification
variable {Ghost : Type}

def InitVC (next : Frame → StepResult) (spec : CheckpointSpecification Ghost) (fuel : Nat)
    (selected : Option (Fin spec.checkpoints.length)) : Prop :=
  ∀ ghost initial, spec.base.contract.pre ghost initial →
    Checkpoint.wp next spec.checkpoints ghost initial selected spec.base.cutpoints
      (spec.base.entryPost ghost initial) fuel initial

def BodyVC (next : Frame → StepResult) (spec : CheckpointSpecification Ghost) (fuel pc : Nat)
    (selected : Option (Fin spec.checkpoints.length)) : Prop :=
  ∀ ghost initial, spec.base.contract.pre ghost initial →
    ∀ current, current.pc = pc → spec.base.invariant ghost initial current →
      Checkpoint.iterationWP next spec.checkpoints ghost initial selected spec.base.cutpoints
        (spec.base.bodyPost ghost initial current) fuel current

def BodiesVC (next : Frame → StepResult) (spec : CheckpointSpecification Ghost) (fuel : Nat)
    (selected : Option (Fin spec.checkpoints.length)) : List Nat → Prop
  | [] => True
  | pc :: rest => spec.BodyVC next fuel pc selected ∧ spec.BodiesVC next fuel selected rest

def SelectedVC (next : Frame → StepResult) (spec : CheckpointSpecification Ghost) (fuel : Nat)
    (index : Fin spec.checkpoints.length) : Prop :=
  spec.InitVC next fuel (some index) ∧ spec.BodiesVC next fuel (some index) spec.base.cutpoints

def CheckpointsVC (next : Frame → StepResult) (spec : CheckpointSpecification Ghost) (fuel : Nat) :
    List (Fin spec.checkpoints.length) → Prop
  | [] => True
  | index :: rest => spec.SelectedVC next fuel index ∧ spec.CheckpointsVC next fuel rest

theorem CheckpointsVC.member {next : Frame → StepResult} {spec : CheckpointSpecification Ghost}
    {fuel : Nat} {index : Fin spec.checkpoints.length} {indices : List (Fin spec.checkpoints.length)}
    (valid : spec.CheckpointsVC next fuel indices) (member : index ∈ indices) : spec.SelectedVC next fuel index := by
  induction indices with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact valid.1
    · exact ih valid.2 member

private theorem bodies_sound {next : Frame → StepResult} {spec : CheckpointSpecification Ghost}
    {fuel : Nat} {pcs : List Nat} (valid : ∀ selected, spec.BodiesVC next fuel selected pcs) :
    spec.base.BodiesVC next fuel pcs := by
  induction pcs with
  | nil => trivial
  | cons pc rest ih =>
    refine ⟨?_, ih (fun selected => (valid selected).2)⟩
    intro ghost initial pre current atPC invariant
    exact Checkpoint.iterationWP_sound (fun selected => (valid selected).1 ghost initial pre current atPC invariant)

/-- Every selected VC is mandatory even when the main goals become vacuous
under its claim. Frame/ownership admission and the original loop rules are retained. -/
def verified {artifact : CPython.V314.Artifact} (admission : Admitted artifact)
    (spec : CheckpointSpecification Ghost) (fuel : Nat) (program : Program)
    (representation : step program = step admission.translation.program)
    (entry : spec.base.EntryVC artifact) (init : spec.InitVC (step program) fuel none)
    (bodies : spec.BodiesVC (step program) fuel none spec.base.cutpoints)
    (checks : spec.CheckpointsVC (step program) fuel (List.finRange spec.checkpoints.length)) :
    VerifiedArtifact artifact spec.base.contract spec.base.mode := by
  have selected := fun index => checks.member (List.mem_finRange index)
  apply spec.base.verified admission fuel program representation entry
  · intro ghost initial pre
    apply Checkpoint.wp_sound
    intro choice
    cases choice with
    | none => exact init ghost initial pre
    | some index => exact (selected index).1 ghost initial pre
  · apply bodies_sound
    intro choice
    cases choice with
    | none => exact bodies
    | some index => exact (selected index).2

end CheckpointSpecification
end VeriPyAsm.Verification.VC
