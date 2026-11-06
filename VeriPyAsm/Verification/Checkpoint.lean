import VeriPyAsm.Verification.Block

/-! Logical checkpoints strengthen facts at the current frame, without changing
the bytecode or execution relation. Their incoming obligation is a separate
premise: the suffix may use a claim only after that obligation is established.
Finite composition does not require a new loop rank or a runtime instruction.
-/

namespace VeriPyAsm.Verification

open Semantics

/-- The context must come from the incoming segment, not from the claim itself.
Outer Lean binders can retain function/loop-entry ghosts and old frames. -/
def CheckpointVC (context claim : Frame → Prop) : Prop :=
  ∀ current, context current → claim current

variable {next : Frame → StepResult} {cuts exits : Nat → Prop}
    {pre context claim : Frame → Prop} {post : Postcondition}

/-- Returns and exceptions bypass the checkpoint and still satisfy `post`.
Only a continuing exit supplies its current-frame fact to the suffix. -/
theorem BlockPartialCorrect.checkpoint
    (first : BlockPartialCorrect next cuts pre { post with continues := context })
    (establish : CheckpointVC context claim)
    (suffix : BlockPartialCorrect next exits (fun s => context s ∧ claim s) post)
    (contains : ∀ pc, exits pc → cuts pc) :
    BlockPartialCorrect next exits pre post := by
  apply first.seq (suffix.consequence (fun s h => ⟨h, establish s h⟩) (fun _ h => h)) contains

/-- Both segments terminate. A zero-step logical checkpoint supplies no evidence
of progress for a loop; nonempty iteration and ranking rules remain separate. -/
theorem BlockTotalCorrect.checkpoint
    (first : BlockTotalCorrect next cuts pre { post with continues := context })
    (establish : CheckpointVC context claim)
    (suffix : BlockTotalCorrect next exits (fun s => context s ∧ claim s) post)
    (contains : ∀ pc, exits pc → cuts pc) :
    BlockTotalCorrect next exits pre post := by
  apply first.seq (suffix.consequence (fun s h => ⟨h, establish s h⟩) (fun _ h => h)) contains

end VeriPyAsm.Verification
