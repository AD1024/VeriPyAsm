import VeriPyAsm.Verification.VC.Scoped
import VeriPyAsm.Verification.VC.EdgeCheckpoint

/-! Checkpoints through scoped loop summaries. Continuations carry every proof
view: selecting a checkpoint must not erase obligations after an inner loop.
Combining the views recovers the original scoped WP with the same fuel, summary
depth, entry snapshots, and local ranking obligations. -/

namespace VeriPyAsm.Verification.VC
open Semantics

namespace Checkpoint
variable {Ghost : Type}

/-- A continuation can contain downstream checkpoint obligations, so it cannot
be replaced by `True` in a selected view. Only ordinary halted requirements are
checked by the main view alone. -/
structure PostMerge {Label : Type} (posts : Option Label → Postcondition)
    (post : Postcondition) : Prop where
  continues : ∀ s, (∀ selected, (posts selected).continues s) → post.continues s
  halted : ∀ outcome, (posts none).Accepts (.halted outcome) → post.Accepts (.halted outcome)

def SummaryMerge {Label : Type} (summaries : Option Label → Summary)
    (summary : Summary) : Prop :=
  ∀ cuts posts post, PostMerge posts post →
    ∀ s, (∀ selected, summaries selected cuts (posts selected) s) → summary cuts post s

def regionWP (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (ghost : Ghost) (initial : Frame) (selected : Option (Fin checks.length))
    (headers : List Nat) (summary : Summary) (cuts : List Nat) (post : Postcondition) :
    Nat → Frame → Prop
  | 0, s => if cuts.contains s.pc then post.continues s else terminal selected False
  | fuel + 1, s =>
    if cuts.contains s.pc then post.continues s
    else if headers.contains s.pc then
      summary cuts { post with
        continues := regionWP next checks ghost initial selected headers summary cuts post fuel } s
    else match next s with
      | .next current => edgeChecks next checks ghost initial selected s current
          (regionWP next checks ghost initial selected headers summary cuts post fuel current)
          (List.finRange checks.length)
      | .halted outcome => terminal selected (post.Accepts (.halted outcome))

def iterationRegionWP (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (ghost : Ghost) (initial : Frame) (selected : Option (Fin checks.length))
    (headers : List Nat) (summary : Summary) (cuts : List Nat) (post : Postcondition)
    (fuel : Nat) (s : Frame) : Prop :=
  match next s with
  | .next current => edgeChecks next checks ghost initial selected s current
      (regionWP next checks ghost initial selected headers summary cuts post fuel current)
      (List.finRange checks.length)
  | .halted outcome => terminal selected (post.Accepts (.halted outcome))

theorem regionWP_sound {next : Frame → StepResult} {checks : List (EdgeCheckpoint Ghost)}
    {ghost : Ghost} {initial : Frame} {headers cuts : List Nat}
    {summaries : Option (Fin checks.length) → Summary} {summary : Summary}
    (mergeSummary : SummaryMerge summaries summary)
    {posts : Option (Fin checks.length) → Postcondition} {post : Postcondition}
    (mergePost : PostMerge posts post) (fuel : Nat) (s : Frame)
    (valid : ∀ selected, regionWP next checks ghost initial selected headers
      (summaries selected) cuts (posts selected) fuel s) :
    VC.regionWP next headers summary cuts post fuel s := by
  induction fuel generalizing s with
  | zero =>
    by_cases atCut : cuts.contains s.pc = true
    · exact ⟨atCut, mergePost.continues s (fun selected => by
        simpa only [regionWP, atCut, ↓reduceIte] using valid selected)⟩
    · have impossible := valid none
      simp only [regionWP, atCut, Bool.false_eq_true, ↓reduceIte, terminal] at impossible
  | succ fuel ih =>
    by_cases atCut : cuts.contains s.pc = true
    · simpa only [VC.regionWP, atCut, ↓reduceIte] using
        mergePost.continues s (fun selected => by
          simpa only [regionWP, atCut, ↓reduceIte] using valid selected)
    · by_cases atHeader : headers.contains s.pc = true
      · simp only [VC.regionWP, atCut, atHeader, Bool.false_eq_true, ↓reduceIte]
        refine mergeSummary cuts
          (fun selected => { posts selected with
            continues := regionWP next checks ghost initial selected headers (summaries selected) cuts
              (posts selected) fuel }) _ ?_ s ?_
        · refine ⟨fun current all => ih current all, ?_⟩
          intro outcome allowed
          cases outcome with
          | returned value final => exact mergePost.halted (.returned value final) allowed
          | raised exception final => exact mergePost.halted (.raised exception final) allowed
          | fault reason final => exact mergePost.halted (.fault reason final) allowed
        · intro selected
          simpa only [regionWP, atCut, atHeader, Bool.false_eq_true, ↓reduceIte] using valid selected
      · simp only [VC.regionWP, atCut, atHeader, Bool.false_eq_true, ↓reduceIte]
        cases transition : next s with
        | next current =>
          apply ih current
          apply edgeChecks_all (next := next) (ghost := ghost) (initial := initial)
            (before := s) (current := current) (indices := List.finRange checks.length)
            (after := fun selected => regionWP next checks ghost initial selected headers
              (summaries selected) cuts (posts selected) fuel current)
          intro selected
          simpa only [regionWP, atCut, atHeader, Bool.false_eq_true, ↓reduceIte, transition]
            using valid selected
        | halted outcome =>
          apply mergePost.halted outcome
          simpa only [regionWP, atCut, atHeader, Bool.false_eq_true, ↓reduceIte, transition, terminal]
            using valid none

theorem iterationRegionWP_sound {next : Frame → StepResult} {checks : List (EdgeCheckpoint Ghost)}
    {ghost : Ghost} {initial s : Frame} {headers cuts : List Nat}
    {summaries : Option (Fin checks.length) → Summary} {summary : Summary}
    (mergeSummary : SummaryMerge summaries summary)
    {posts : Option (Fin checks.length) → Postcondition} {post : Postcondition}
    (mergePost : PostMerge posts post) (fuel : Nat)
    (valid : ∀ selected, iterationRegionWP next checks ghost initial selected headers
      (summaries selected) cuts (posts selected) fuel s) :
    VC.iterationRegionWP next headers summary cuts post fuel s := by
  unfold VC.iterationRegionWP
  cases transition : next s with
  | next current =>
    apply regionWP_sound (next := next) (ghost := ghost) (initial := initial) mergeSummary mergePost fuel current
    apply edgeChecks_all (next := next) (ghost := ghost) (initial := initial)
      (before := s) (current := current) (indices := List.finRange checks.length)
      (after := fun selected => regionWP next checks ghost initial selected headers
        (summaries selected) cuts (posts selected) fuel current)
    intro selected
    simpa only [iterationRegionWP, transition] using valid selected
  | halted outcome =>
    apply mergePost.halted outcome
    simpa only [iterationRegionWP, transition, terminal] using valid none

/-- Backedges check the invariant/rank in the main view. Exits retain the
caller's continuation in every view, including a selected checkpoint after
the loop. No claim is implicitly added to a loop invariant. -/
def bodyPost {checks : List (EdgeCheckpoint Ghost)}
    (selected : Option (Fin checks.length)) (loop : ScopedLoop Ghost)
    (mode : CorrectnessMode) (ghost : Ghost) (initial entry old : Frame)
    (exits : List Nat) (post : Postcondition) : Postcondition :=
  { continues := fun current =>
      if exits.contains current.pc then requirement loop.header .exit (post.continues current)
      else terminal selected (requirement loop.header .preservation (loop.atHeader ghost initial entry current) ∧ (match mode with
        | .partialCorrectness => True
        | .totalCorrectness => requirement loop.header .ranking
            (loop.rank ghost initial current < loop.rank ghost initial old)))
    returned := fun value final => requirement loop.header .exit (post.returned value final)
    raises := fun exception final => requirement loop.header .exit (post.raises exception final) }

theorem bodyPost_merge (checks : List (EdgeCheckpoint Ghost)) (loop : ScopedLoop Ghost)
    (mode : CorrectnessMode) (ghost : Ghost) (initial entry old : Frame) (exits : List Nat)
    {posts : Option (Fin checks.length) → Postcondition} {post : Postcondition}
    (merge : PostMerge posts post) :
    PostMerge (fun selected => bodyPost (checks := checks) selected loop mode ghost initial entry old exits
      (posts selected)) (loop.bodyPost mode ghost initial entry old exits post) := by
  constructor
  · intro current valid
    by_cases atExit : exits.contains current.pc = true
    · simpa only [ScopedLoop.bodyPost, requirement, atExit, ↓reduceIte] using
        merge.continues current (fun selected => by
          simpa only [bodyPost, requirement, atExit, ↓reduceIte] using valid selected)
    · have main := valid none
      cases mode <;>
        simpa only [bodyPost, ScopedLoop.bodyPost, requirement, atExit, Bool.false_eq_true, ↓reduceIte, terminal] using main
  · intro outcome allowed
    cases outcome with
    | returned value final => exact merge.halted (.returned value final) allowed
    | raised exception final => exact merge.halted (.raised exception final) allowed
    | fault reason final => exact merge.halted (.fault reason final) allowed

def loopSummary (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (loops : List (ScopedLoop Ghost)) (mode : CorrectnessMode) (ghost : Ghost)
    (initial : Frame) (selected : Option (Fin checks.length)) (fuel : Nat) : Nat → Summary
  | 0 => fun _ _ _ => terminal selected False
  | depth + 1 => fun cuts post entry =>
    match findLoop loops entry.pc with
    | none => terminal selected False
    | some loop =>
      let exits := cuts ++ loop.exits
      terminal selected (requirement loop.header .initialization
        (¬ exits.contains loop.header = true ∧ loop.atHeader ghost initial entry entry)) ∧
      ∀ current, loop.atHeader ghost initial entry current →
        iterationRegionWP next checks ghost initial selected (loops.map ScopedLoop.header)
          (loopSummary next checks loops mode ghost initial selected fuel depth) (loop.header :: exits)
          (bodyPost (checks := checks) selected loop mode ghost initial entry current exits post) fuel current

theorem loopSummary_sound (next : Frame → StepResult) (checks : List (EdgeCheckpoint Ghost))
    (loops : List (ScopedLoop Ghost)) (mode : CorrectnessMode) (ghost : Ghost)
    (initial : Frame) (fuel depth : Nat) :
    SummaryMerge (fun selected => loopSummary next checks loops mode ghost initial selected fuel depth)
      (VC.loopSummary next loops mode ghost initial fuel depth) := by
  induction depth with
  | zero => intro cuts posts post merge s valid; exact valid none
  | succ depth ih =>
    intro cuts posts post merge entry valid
    unfold VC.loopSummary
    cases found : findLoop loops entry.pc with
    | none => simpa only [loopSummary, found, terminal] using valid none
    | some loop =>
      have entryValid := valid none
      simp only [loopSummary, found, terminal] at entryValid
      refine ⟨entryValid.1.1, entryValid.1.2, ?_⟩
      intro current invariant
      apply iterationRegionWP_sound (next := next) (ghost := ghost) (initial := initial)
        ih (bodyPost_merge checks loop mode ghost initial entry current
        (cuts ++ loop.exits) merge) fuel
      intro selected
      have selectedValid := valid selected
      simp only [loopSummary, found] at selectedValid
      exact selectedValid.2 current invariant

end Checkpoint

structure ScopedCheckpointSpecification (Ghost : Type) where
  base : ScopedSpecification Ghost
  checkpoints : List (EdgeCheckpoint Ghost)

namespace ScopedCheckpointSpecification
variable {Ghost : Type}

def ExecutionVC (next : Frame → StepResult) (spec : ScopedCheckpointSpecification Ghost) (fuel : Nat)
    (selected : Option (Fin spec.checkpoints.length)) : Prop :=
  ∀ ghost initial, spec.base.contract.pre ghost initial →
    Checkpoint.regionWP next spec.checkpoints ghost initial selected spec.base.headers
      (Checkpoint.loopSummary next spec.checkpoints spec.base.loops spec.base.mode ghost initial
        selected fuel spec.base.loops.length) [] (spec.base.post ghost initial) fuel initial

def SelectedVC (next : Frame → StepResult) (spec : ScopedCheckpointSpecification Ghost) (fuel : Nat)
    (index : Fin spec.checkpoints.length) : Prop := spec.ExecutionVC next fuel (some index)

def CheckpointsVC (next : Frame → StepResult) (spec : ScopedCheckpointSpecification Ghost) (fuel : Nat) :
    List (Fin spec.checkpoints.length) → Prop
  | [] => True
  | index :: rest => spec.SelectedVC next fuel index ∧ spec.CheckpointsVC next fuel rest

theorem CheckpointsVC.member {next : Frame → StepResult} {spec : ScopedCheckpointSpecification Ghost}
    {fuel : Nat} {index : Fin spec.checkpoints.length} {indices : List (Fin spec.checkpoints.length)}
    (valid : spec.CheckpointsVC next fuel indices) (member : index ∈ indices) : spec.SelectedVC next fuel index := by
  induction indices with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact valid.1
    · exact ih valid.2 member

/-- Reuse the existing scoped assembly, including admission, entry compatibility,
independent loop ranks, and termination of each invoked summary. -/
def verified {artifact : CPython.V314.Artifact} (admission : Admitted artifact)
    (spec : ScopedCheckpointSpecification Ghost) (fuel : Nat) (program : Program)
    (representation : step program = step admission.translation.program)
    (entry : spec.base.EntryVC artifact) (execution : spec.ExecutionVC (step program) fuel none)
    (checks : spec.CheckpointsVC (step program) fuel (List.finRange spec.checkpoints.length)) :
    VerifiedArtifact artifact spec.base.contract spec.base.mode := by
  apply spec.base.verified admission fuel program representation entry
  intro ghost initial pre
  apply Checkpoint.regionWP_sound (next := step program) (ghost := ghost) (initial := initial)
    (posts := fun _ => spec.base.post ghost initial)
    (Checkpoint.loopSummary_sound (step program) spec.checkpoints spec.base.loops spec.base.mode
      ghost initial fuel spec.base.loops.length)
    ⟨fun _ all => all none, fun _ allowed => allowed⟩ fuel initial
  intro selected
  cases selected with
  | none => exact execution ghost initial pre
  | some index => exact (checks.member (List.mem_finRange index)) ghost initial pre

end ScopedCheckpointSpecification
end VeriPyAsm.Verification.VC
