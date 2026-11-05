import VeriPyAsm.Semantics.Machine

/-! Fuel-independent finite executions and reachability for the deterministic
single-frame semantics. Terminal outcomes include Python exceptions and VM
faults; a contract decides which outcomes are allowed. Reachability contains only
continuing transitions, so a halted frame cannot silently resume execution.

The equivalences with `run` connect symbolic execution proofs to the executable
evaluator. Exhaustion witnesses a reachable continuation, not termination. -/

namespace VeriPyAsm.Semantics

/-- A finite sequence of continuing transitions followed by one terminal step. -/
inductive Executes (next : Frame → StepResult) : Frame → Halt → Prop where
  | halt {s : Frame} {outcome : Halt} :
      next s = .halted outcome → Executes next s outcome
  | step {s s' : Frame} {outcome : Halt} :
      next s = .next s' → Executes next s' outcome → Executes next s outcome

/-- Zero or more continuing transitions. Terminal transitions are excluded. -/
inductive Reaches (next : Frame → StepResult) : Frame → Frame → Prop where
  | refl (s : Frame) : Reaches next s s
  | step {s s' t : Frame} :
      next s = .next s' → Reaches next s' t → Reaches next s t

variable {next : Frame → StepResult} {s t u : Frame} {outcome : Halt}

theorem Executes.to_run (execution : Executes next s outcome) :
    ∃ fuel, run next fuel s = .halted outcome := by
  induction execution with
  | halt h => exact ⟨1, by simp [run, h]⟩
  | step h _ ih =>
    obtain ⟨fuel, hrun⟩ := ih
    exact ⟨fuel + 1, by simp [run, h, hrun]⟩

theorem Executes.of_run {fuel : Nat} (execution : run next fuel s = .halted outcome) :
    Executes next s outcome := by
  induction fuel generalizing s with
  | zero => cases execution
  | succ fuel ih =>
    cases h : next s with
    | halted result =>
      simp only [run, h] at execution
      cases execution
      exact .halt h
    | next s' =>
      simp only [run, h] at execution
      exact .step h (ih execution)

theorem executes_iff_run :
    Executes next s outcome ↔ ∃ fuel, run next fuel s = .halted outcome :=
  ⟨Executes.to_run, fun ⟨_, h⟩ => Executes.of_run h⟩

/-- Determinism includes the entire terminal frame, not just the return value. -/
theorem Executes.deterministic {other : Halt}
    (first : Executes next s outcome) (second : Executes next s other) : outcome = other := by
  induction first with
  | halt h =>
    cases second with
    | halt h' => exact StepResult.halted.inj (h.symm.trans h')
    | step h' _ => cases h.symm.trans h'
  | step h _ ih =>
    cases second with
    | halt h' => cases h.symm.trans h'
    | step h' tail =>
      have equal := StepResult.next.inj (h.symm.trans h')
      cases equal
      exact ih tail

/-- Extra fuel cannot change an already observed terminal outcome. -/
theorem run_halted_add {fuel : Nat}
    (execution : run next fuel s = .halted outcome) (extra : Nat) :
    run next (fuel + extra) s = .halted outcome := by
  induction fuel generalizing s with
  | zero => cases execution
  | succ fuel ih =>
    cases h : next s with
    | halted result =>
      simp only [run, h] at execution
      simpa [Nat.succ_add, run, h] using execution
    | next s' =>
      simp only [run, h] at execution
      simpa [Nat.succ_add, run, h] using ih execution

theorem run_halted_of_le {fuel larger : Nat}
    (execution : run next fuel s = .halted outcome) (bound : fuel ≤ larger) :
    run next larger s = .halted outcome := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  exact run_halted_add execution extra

theorem Reaches.trans (first : Reaches next s t) (second : Reaches next t u) :
    Reaches next s u := by
  induction first with
  | refl => exact second
  | step h _ ih => exact .step h (ih second)

/-- Prepend a path of continuing transitions to a terminal execution. -/
theorem Reaches.executes (path : Reaches next s t) (execution : Executes next t outcome) :
    Executes next s outcome := by
  induction path with
  | refl => exact execution
  | step h _ ih => exact .step h (ih execution)

theorem Reaches.to_run (path : Reaches next s t) :
    ∃ fuel, run next fuel s = .exhausted t := by
  induction path with
  | refl => exact ⟨0, rfl⟩
  | step h _ ih =>
    obtain ⟨fuel, hrun⟩ := ih
    exact ⟨fuel + 1, by simp [run, h, hrun]⟩

theorem Reaches.of_run {fuel : Nat} (execution : run next fuel s = .exhausted t) :
    Reaches next s t := by
  induction fuel generalizing s with
  | zero =>
    cases execution
    exact .refl _
  | succ fuel ih =>
    cases h : next s with
    | halted result => simp [run, h] at execution
    | next s' =>
      simp only [run, h] at execution
      exact .step h (ih execution)

theorem reaches_iff_run_exhausted :
    Reaches next s t ↔ ∃ fuel, run next fuel s = .exhausted t :=
  ⟨Reaches.to_run, fun ⟨_, h⟩ => Reaches.of_run h⟩

end VeriPyAsm.Semantics
