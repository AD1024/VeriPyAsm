import VeriPyAsm.Verification.Checkpoint
import VeriPyAsm.Verification.VC.WeakestPrecondition

/-! Proof-producing segment cuts for the existing weakest precondition. Segment
bounds add under composition; checkpoints do not consume a VM step or invent
progress. In particular, `iterationWP` still executes its initial instruction.
These rules let separately named incoming and downstream VCs assemble into the
same semantic WP used by the existing loop and final-artifact rules.
-/

namespace VeriPyAsm.Verification.VC

open Semantics

variable {next : Frame → StepResult} {cuts exits : List Nat}
    {post : Postcondition} {context claim : Frame → Prop}
    {fuel prefixFuel suffixFuel : Nat} {initial : Frame}

theorem wp_more (valid : wp next cuts post fuel initial) (extra : Nat) :
    wp next cuts post (fuel + extra) initial := by
  induction fuel generalizing initial with
  | zero =>
    rcases valid with ⟨atCut, allowed⟩
    simp only [Nat.zero_add]
    cases extra with
    | zero => exact ⟨atCut, allowed⟩
    | succ extra => simpa only [wp, atCut, ↓reduceIte] using allowed
  | succ fuel ih =>
    by_cases atCut : cuts.contains initial.pc = true
    · simpa only [wp, Nat.succ_add, atCut, ↓reduceIte] using valid
    · simp only [wp, Nat.succ_add, atCut, Bool.false_eq_true, ↓reduceIte] at valid ⊢
      cases transition : next initial with
      | next current => simp only [transition] at valid ⊢; exact ih valid
      | halted outcome => simpa only [transition] using valid

/-- Rejoin a finite prefix and suffix, including first-exit behavior and early
halts. Every final exit must also stop the prefix. No CFG oracle is assumed. -/
theorem wp_seq
    (first : wp next cuts { post with continues := context } prefixFuel initial)
    (suffix : ∀ current, context current → wp next exits post suffixFuel current)
    (contains : ∀ pc, exits.contains pc = true → cuts.contains pc = true) :
    wp next exits post (prefixFuel + suffixFuel) initial := by
  induction prefixFuel generalizing initial with
  | zero => simpa only [Nat.zero_add] using suffix initial first.2
  | succ fuel ih =>
    by_cases atCut : cuts.contains initial.pc = true
    · have allowed : context initial := by simpa only [wp, atCut, ↓reduceIte] using first
      simpa only [Nat.add_comm suffixFuel] using wp_more (suffix initial allowed) (fuel + 1)
    · have outside : ¬ exits.contains initial.pc = true := fun h => atCut (contains _ h)
      simp only [wp, atCut, Bool.false_eq_true, ↓reduceIte] at first
      simp only [Nat.succ_add, wp, outside, Bool.false_eq_true, ↓reduceIte]
      cases transition : next initial with
      | next current => simp only [transition] at first ⊢; exact ih first
      | halted outcome =>
        simp only [transition] at first ⊢
        cases outcome <;> exact first

/-- The incoming claim is a mandatory premise. The suffix receives it about
the same frame that the prefix reached; later writes cannot reuse it unchanged. -/
theorem wp_checkpoint
    (first : wp next cuts { post with continues := context } prefixFuel initial)
    (establish : CheckpointVC context claim)
    (suffix : ∀ current, context current ∧ claim current → wp next exits post suffixFuel current)
    (contains : ∀ pc, exits.contains pc = true → cuts.contains pc = true) :
    wp next exits post (prefixFuel + suffixFuel) initial :=
  wp_seq first (fun s h => suffix s ⟨h, establish s h⟩) contains

/-- Splitting after the initial step cannot turn a nonempty iteration into a
zero-step proof. The original rank comparison can remain in `post`. -/
theorem iterationWP_checkpoint
    (first : iterationWP next cuts { post with continues := context } prefixFuel initial)
    (establish : CheckpointVC context claim)
    (suffix : ∀ current, context current ∧ claim current → wp next exits post suffixFuel current)
    (contains : ∀ pc, exits.contains pc = true → cuts.contains pc = true) :
    iterationWP next exits post (prefixFuel + suffixFuel) initial := by
  unfold iterationWP at first ⊢
  cases transition : next initial with
  | next current =>
    simp only [transition] at first ⊢
    exact wp_checkpoint first establish suffix contains
  | halted outcome =>
    simp only [transition] at first ⊢
    cases outcome <;> exact first

end VeriPyAsm.Verification.VC
