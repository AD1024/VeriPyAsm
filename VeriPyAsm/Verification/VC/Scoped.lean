import VeriPyAsm.Verification.VC.WeakestPrecondition

/-! Compositional weakest preconditions for nested loops. A loop is summarized
through its own invariant and ranking; its body may use summaries of inner
loops. Depth bounds proof construction, not execution. Fuel bounds only an
acyclic region between summaries. Every loop iteration executes a real step.
-/

namespace VeriPyAsm.Verification.VC

open Semantics

abbrev Summary := List Nat → Postcondition → Frame → Prop

def regionWP (next : Frame → StepResult) (headers : List Nat) (summary : Summary)
    (cuts : List Nat) (post : Postcondition) : Nat → Frame → Prop
  | 0, s => cuts.contains s.pc = true ∧ post.continues s
  | fuel + 1, s =>
    if cuts.contains s.pc then post.continues s
    else if headers.contains s.pc then
      summary cuts { post with continues := regionWP next headers summary cuts post fuel } s
    else match next s with
      | .next current => regionWP next headers summary cuts post fuel current
      | .halted outcome => post.Accepts (.halted outcome)

def iterationRegionWP (next : Frame → StepResult) (headers : List Nat) (summary : Summary)
    (cuts : List Nat) (post : Postcondition) (fuel : Nat) (s : Frame) : Prop :=
  match next s with
  | .next current => regionWP next headers summary cuts post fuel current
  | .halted outcome => post.Accepts (.halted outcome)

def SummaryPartial (next : Frame → StepResult) (extra : Frame → List Nat) (summary : Summary) : Prop :=
  ∀ cuts post s, summary cuts post s →
    BlockPartialCorrect next (fun pc => (cuts ++ extra s).contains pc = true) (fun t => t = s) post

def SummaryTotal (next : Frame → StepResult) (extra : Frame → List Nat) (summary : Summary) : Prop :=
  ∀ cuts post s, summary cuts post s →
    BlockTotalCorrect next (fun pc => (cuts ++ extra s).contains pc = true) (fun t => t = s) post

private theorem contains_left (cuts extra : List Nat) (pc : Nat)
    (h : cuts.contains pc = true) : (cuts ++ extra).contains pc = true := by
  simp only [List.contains_append, h, Bool.true_or]

theorem regionWP_partial {next : Frame → StepResult} {headers : List Nat}
    {summary : Summary} {extra : Frame → List Nat} (sound : SummaryPartial next extra summary)
    (cuts : List Nat) (post : Postcondition) (fuel : Nat) :
    BlockPartialCorrect next (fun pc => cuts.contains pc = true)
      (regionWP next headers summary cuts post fuel) post := by
  induction fuel with
  | zero =>
    intro s valid result execution
    have equal := execution.deterministic (.exit valid.1)
    subst result
    exact valid.2
  | succ fuel ih =>
    intro s valid result execution
    by_cases atCut : cuts.contains s.pc = true
    · have equal := execution.deterministic (.exit atCut)
      subst result
      simpa only [regionWP, atCut, Bool.false_eq_true, ↓reduceIte, Postcondition.Accepts] using valid
    · by_cases header : headers.contains s.pc = true
      · have first := sound cuts { post with continues := regionWP next headers summary cuts post fuel }
          s (by simpa only [regionWP, atCut, header, Bool.false_eq_true, ↓reduceIte] using valid)
        exact (first.seq ih (contains_left cuts (extra s))) s rfl result execution
      · simp only [regionWP, atCut, header, Bool.false_eq_true, ↓reduceIte] at valid
        cases execution with
        | exit h => exact (atCut h).elim
        | halt _ transition => rw [transition] at valid; exact valid
        | step _ transition after => rw [transition] at valid; exact ih _ valid _ after

theorem regionWP_total {next : Frame → StepResult} {headers : List Nat}
    {summary : Summary} {extra : Frame → List Nat} (sound : SummaryTotal next extra summary)
    (cuts : List Nat) (post : Postcondition) (fuel : Nat) :
    BlockTotalCorrect next (fun pc => cuts.contains pc = true)
      (regionWP next headers summary cuts post fuel) post := by
  induction fuel with
  | zero => exact .exit (fun _ h => h.1) (fun _ h => h.2)
  | succ fuel ih =>
    apply BlockTotalCorrect.of_execution
    intro s valid
    by_cases atCut : cuts.contains s.pc = true
    · exact ⟨.next s, .exit atCut, by simpa only [regionWP, atCut, Bool.false_eq_true, ↓reduceIte, Postcondition.Accepts] using valid⟩
    · by_cases header : headers.contains s.pc = true
      · have first := sound cuts { post with continues := regionWP next headers summary cuts post fuel }
          s (by simpa only [regionWP, atCut, header, Bool.false_eq_true, ↓reduceIte] using valid)
        have complete := first.seq ih (contains_left cuts (extra s))
        obtain ⟨result, execution⟩ := complete.terminates s rfl
        exact ⟨result, execution, complete.partialCorrect s rfl result execution⟩
      · simp only [regionWP, atCut, header, Bool.false_eq_true, ↓reduceIte] at valid
        cases transition : next s with
        | next current =>
          rw [transition] at valid
          obtain ⟨result, execution⟩ := ih.terminates current valid
          exact ⟨result, .step atCut transition execution, ih.partialCorrect current valid result execution⟩
        | halted outcome =>
          rw [transition] at valid
          exact ⟨.halted outcome, .halt atCut transition, valid⟩

theorem iterationRegionWP_partial {next : Frame → StepResult} {headers : List Nat}
    {summary : Summary} {extra : Frame → List Nat} (sound : SummaryPartial next extra summary)
    (cuts : List Nat) (post : Postcondition) (fuel : Nat) :
    IterationPartialCorrect next (fun pc => cuts.contains pc = true)
      (iterationRegionWP next headers summary cuts post fuel) post := by
  intro s valid result execution
  unfold iterationRegionWP at valid
  cases execution with
  | halt transition => rw [transition] at valid; exact valid
  | step transition after =>
    rw [transition] at valid
    exact regionWP_partial sound cuts post fuel _ valid _ after

theorem iterationRegionWP_total {next : Frame → StepResult} {headers : List Nat}
    {summary : Summary} {extra : Frame → List Nat} (sound : SummaryTotal next extra summary)
    (cuts : List Nat) (post : Postcondition) (fuel : Nat) :
    IterationTotalCorrect next (fun pc => cuts.contains pc = true)
      (iterationRegionWP next headers summary cuts post fuel) post := by
  apply IterationTotalCorrect.of_execution
  intro s valid
  unfold iterationRegionWP at valid
  cases transition : next s with
  | next current =>
    rw [transition] at valid
    have tail := regionWP_total (headers := headers) sound cuts post fuel
    obtain ⟨result, execution⟩ := tail.terminates current valid
    exact ⟨result, .step transition execution, tail.partialCorrect current valid result execution⟩
  | halted outcome =>
    rw [transition] at valid
    exact ⟨.halted outcome, .halt transition, valid⟩

structure ScopedLoop (Ghost : Type) where
  header : Nat
  exits : List Nat
  /-- Arguments are ghost, function entry, loop entry, and current frame. The
  loop-entry frame supports proved framing of locals not written by the loop. -/
  invariant : Ghost → Frame → Frame → Frame → Prop
  ranking : Option (Ghost → Frame → Frame → Nat) := none

def findLoop {Ghost : Type} : List (ScopedLoop Ghost) → Nat → Option (ScopedLoop Ghost)
  | [], _ => none
  | loop :: rest, pc => if loop.header == pc then some loop else findLoop rest pc

def loopExits {Ghost : Type} (loops : List (ScopedLoop Ghost)) (s : Frame) : List Nat :=
  ((findLoop loops s.pc).map ScopedLoop.exits).getD []

def ScopedLoop.atHeader {Ghost : Type} (loop : ScopedLoop Ghost) (ghost : Ghost)
    (initial entry current : Frame) : Prop :=
  current.pc = loop.header ∧ loop.invariant ghost initial entry current

def ScopedLoop.rank {Ghost : Type} (loop : ScopedLoop Ghost) (ghost : Ghost)
    (initial current : Frame) : Nat :=
  (loop.ranking.getD (fun _ _ _ => 0)) ghost initial current

def ScopedLoop.bodyPost {Ghost : Type} (loop : ScopedLoop Ghost) (mode : CorrectnessMode)
    (ghost : Ghost) (initial entry old : Frame) (exits : List Nat) (post : Postcondition) : Postcondition :=
  { post with continues := fun current =>
      if exits.contains current.pc then post.continues current
      else (loop.atHeader ghost initial entry current ∧ (match mode with
        | .partialCorrectness => True
        | .totalCorrectness => loop.rank ghost initial current < loop.rank ghost initial old)) }

def loopSummary {Ghost : Type} (next : Frame → StepResult) (loops : List (ScopedLoop Ghost))
    (mode : CorrectnessMode) (ghost : Ghost) (initial : Frame) (fuel : Nat) : Nat → Summary
  | 0 => fun _ _ _ => False
  | depth + 1 => fun cuts post entry =>
    match findLoop loops entry.pc with
    | none => False
    | some loop =>
      let exits := cuts ++ loop.exits
      ¬ exits.contains loop.header = true ∧ loop.atHeader ghost initial entry entry ∧
      ∀ current, loop.atHeader ghost initial entry current →
        iterationRegionWP next (loops.map ScopedLoop.header)
          (loopSummary next loops mode ghost initial fuel depth) (loop.header :: exits)
          (loop.bodyPost mode ghost initial entry current exits post) fuel current

private theorem header_contains (header : Nat) (exits : List Nat) (pc : Nat)
    (h : exits.contains pc = true) : (header :: exits).contains pc = true := by
  simp only [List.contains_cons, h, Bool.or_true]

theorem loopSummary_partial {Ghost : Type} (next : Frame → StepResult)
    (loops : List (ScopedLoop Ghost)) (mode : CorrectnessMode) (ghost : Ghost)
    (initial : Frame) (fuel depth : Nat) :
    SummaryPartial next (loopExits loops) (loopSummary next loops mode ghost initial fuel depth) := by
  induction depth with
  | zero => intro cuts post entry valid; exact valid.elim
  | succ depth ih =>
    intro cuts post entry valid
    unfold loopSummary at valid
    cases found : findLoop loops entry.pc with
    | none => simp only [found] at valid
    | some loop =>
      simp only [found] at valid
      obtain ⟨outside, invariant, body⟩ := valid
      have correct : BlockPartialCorrect next (fun pc => (cuts ++ loop.exits).contains pc = true)
          (loop.atHeader ghost initial entry) post := by
        apply BlockPartialCorrect.loop (I := loop.atHeader ghost initial entry) (cuts := fun pc => (loop.header :: (cuts ++ loop.exits)).contains pc = true)
          (header_contains loop.header _) (fun s h atExit => outside (h.1 ▸ atExit))
        intro s pre result execution
        have allowed := iterationRegionWP_partial ih _ _ fuel s (body s pre) result execution
        cases result with
        | next frame =>
          by_cases atExit : (cuts ++ loop.exits).contains frame.pc = true
          · exact Or.inl ⟨atExit, by simpa only [Postcondition.Accepts, ScopedLoop.bodyPost,
              atExit, ↓reduceIte] using allowed⟩
          · simp only [Postcondition.Accepts, ScopedLoop.bodyPost,
              atExit, Bool.false_eq_true, ↓reduceIte] at allowed
            exact Or.inr allowed.1
        | halted outcome => cases outcome <;> exact allowed
      simpa only [loopExits, found, Option.map_some, Option.getD_some] using
        (correct.consequence (P' := fun s => s = entry)
          (fun s equal => by subst s; exact invariant) (fun _ h => h))

theorem loopSummary_total {Ghost : Type} (next : Frame → StepResult)
    (loops : List (ScopedLoop Ghost)) (ghost : Ghost) (initial : Frame) (fuel depth : Nat) :
    SummaryTotal next (loopExits loops)
      (loopSummary next loops .totalCorrectness ghost initial fuel depth) := by
  induction depth with
  | zero => intro cuts post entry valid; exact valid.elim
  | succ depth ih =>
    intro cuts post entry valid
    unfold loopSummary at valid
    cases found : findLoop loops entry.pc with
    | none => simp only [found] at valid
    | some loop =>
      simp only [found] at valid
      obtain ⟨outside, invariant, body⟩ := valid
      have correct : BlockTotalCorrect next (fun pc => (cuts ++ loop.exits).contains pc = true)
          (loop.atHeader ghost initial entry) post := by
        apply BlockTotalCorrect.loop (I := loop.atHeader ghost initial entry) (cuts := fun pc => (loop.header :: (cuts ++ loop.exits)).contains pc = true)
          (loop.rank ghost initial) (header_contains loop.header _)
          (fun s h atExit => outside (h.1 ▸ atExit))
        intro s pre
        exact (iterationRegionWP_total (headers := loops.map ScopedLoop.header) ih _ _ fuel).consequence
          (fun t equal => by subst t; exact body s pre) (fun result allowed => by
            cases result with
            | next frame =>
              by_cases atExit : (cuts ++ loop.exits).contains frame.pc = true
              · exact Or.inl ⟨atExit, by simpa only [Postcondition.Accepts, ScopedLoop.bodyPost,
                  atExit, ↓reduceIte] using allowed⟩
              · exact Or.inr (by simpa only [Postcondition.Accepts, ScopedLoop.bodyPost,
                  atExit, Bool.false_eq_true, ↓reduceIte] using allowed)
            | halted outcome => cases outcome <;> exact allowed)
      simpa only [loopExits, found, Option.map_some, Option.getD_some] using
        (correct.consequence (P' := fun s => s = entry)
          (fun s equal => by subst s; exact invariant) (fun _ h => h))

structure ScopedSpecification (Ghost : Type) where
  contract : Contract Ghost
  mode : CorrectnessMode := .totalCorrectness
  loops : List (ScopedLoop Ghost)

namespace ScopedSpecification

variable {Ghost : Type}

def headers (spec : ScopedSpecification Ghost) : List Nat := spec.loops.map ScopedLoop.header

def post (spec : ScopedSpecification Ghost) (ghost : Ghost) (initial : Frame) : Postcondition where
  returned := spec.contract.post ghost initial
  raises := spec.contract.raises ghost initial

def EntryVC (artifact : CPython.V314.Artifact) (spec : ScopedSpecification Ghost) : Prop :=
  ∀ ghost initial, spec.contract.pre ghost initial → EntryFrame artifact initial

def ExecutionVC (next : Frame → StepResult) (spec : ScopedSpecification Ghost) (fuel : Nat) : Prop :=
  ∀ ghost initial, spec.contract.pre ghost initial →
    regionWP next spec.headers
      (loopSummary next spec.loops spec.mode ghost initial fuel spec.loops.length)
      [] (spec.post ghost initial) fuel initial

def verified {artifact : CPython.V314.Artifact}
    (admission : Admitted artifact) (spec : ScopedSpecification Ghost) (fuel : Nat)
    (program : Program) (representation : step program = step admission.translation.program)
    (entry : spec.EntryVC artifact) (execution : spec.ExecutionVC (step program) fuel) :
    VerifiedArtifact artifact spec.contract spec.mode where
  admission := admission
  entry := entry
  correctness := by
    rw [← representation]
    cases mode : spec.mode with
    | partialCorrectness =>
      intro ghost initial pre outcome path
      have correct := regionWP_partial (headers := spec.headers)
        (loopSummary_partial (step program) spec.loops spec.mode ghost initial fuel spec.loops.length)
        [] (spec.post ghost initial) fuel
      have allowed := correct initial (execution ghost initial pre) (.halted outcome)
        (by simpa using BlockExecutes.of_execution path)
      cases outcome <;> exact allowed
    | totalCorrectness =>
      apply TotalCorrect.of_execution
      intro ghost initial pre
      have correct := regionWP_total (headers := spec.headers)
        (loopSummary_total (step program) spec.loops ghost initial fuel spec.loops.length)
        [] (spec.post ghost initial) fuel
      have valid := execution ghost initial pre
      rw [mode] at valid
      obtain ⟨result, path⟩ := correct.terminates initial valid
      have allowed := correct.partialCorrect initial valid result path
      cases result with
      | next frame => exact (by simpa using path.exit_at : False).elim
      | halted outcome =>
        refine ⟨outcome, path.halts, ?_⟩
        cases outcome <;> exact allowed

end ScopedSpecification
end VeriPyAsm.Verification.VC
