import VeriPyAsm.Examples.Assertions.Artifact
import VeriPyAsm.Verification.VC.Checkpoint
import VeriPyAsm.Verification.VC.Manifest

/-! Native checkpoint interface over the actual `nonnegative` assertion artifact.
The runtime assertion must reach byte 20 without raising. A separate logical
hint proves `1 ≤ n + 1` there; the return segment may then use that proved fact.
The manifest is explicit in this milestone, not emitted from Python comments.
This module imports no proof provider.
-/

namespace VeriPyAsm.Examples.Checkpoints

open Semantics Verification

def entryFrame (n : Int) : Frame := { locals := [some (.int n)] }

def contract : Contract Int where
  pre n initial := 0 ≤ n ∧ initial = entryFrame n
  post n _ value final :=
    value = .int n ∧ 1 ≤ n + 1 ∧ final.locals = [some (.int n)] ∧ final.stack = []
  raises _ _ _ _ := False

def specification : Verification.VC.Specification Int where
  contract := contract

def post (n : Int) : Postcondition := specification.post n (entryFrame n)

/-- The incoming fact belongs to the assertion's passing continuation. -/
def context (n : Int) (current : Frame) : Prop :=
  current = { pc := 20, locals := [some (.int n)] } ∧ 0 ≤ n

def hintVC (claim : Int → Prop) : Prop :=
  ∀ n, CheckpointVC (context n) (fun _ => claim n)

def finishVC (claim : Int → Prop) : Prop :=
  ∀ n current, context n current ∧ claim n →
    Verification.VC.wp (step Assertions.nonnegative.translation.program) [] (post n) 2 current

namespace VC

def entry : Prop := specification.EntryVC Assertions.nonnegativeArtifact

def runtimeAssertion : Prop :=
  ∀ n, 0 ≤ n → Verification.VC.wp (step Assertions.nonnegative.translation.program)
    [20] { post n with continues := context n } 10 (entryFrame n)

def hint : Prop := ∀ n : Int, 0 ≤ n → 1 ≤ n + 1

/-- Remove the concrete frame from the arithmetic handoff, retaining checked
evidence that this is exactly the semantic incoming checkpoint obligation. -/
theorem hint.normalization : hintVC (fun n => 1 ≤ n + 1) = hint := by
  apply propext
  constructor
  · intro valid n nonnegative
    exact valid n { pc := 20, locals := [some (.int n)] } ⟨rfl, nonnegative⟩
  · intro valid n current incoming
    exact valid n incoming.2

def finish : Prop := finishVC (fun n => 1 ≤ n + 1)

structure Proofs : Prop where
  entry : entry
  runtimeAssertion : runtimeAssertion
  hint : hint
  finish : finish

end VC

/-- The claim is a parameter so regressions can substitute a false hint while
retaining the identical execution and assembly rules. No proof is inferred here. -/
def assembleUsing (claim : Int → Prop) (entry : VC.entry)
    (runtimeAssertion : VC.runtimeAssertion) (hint : hintVC claim) (finish : finishVC claim) :
    VerifiedArtifact Assertions.nonnegativeArtifact contract := by
  apply Verification.VC.Specification.verified Assertions.nonnegative specification 12
    Assertions.nonnegative.translation.program rfl entry ?_ True.intro
  rintro n initial ⟨nonnegative, rfl⟩
  have noCuts : specification.atCut n (entryFrame n) = fun _ => False := by
    funext current
    simp [Verification.VC.Specification.atCut, specification]
  have samePost : specification.entryPost n (entryFrame n) = post n := by
    unfold Verification.VC.Specification.entryPost post
    rw [noCuts]
    rfl
  rw [samePost]
  exact Verification.VC.wp_checkpoint (runtimeAssertion n nonnegative) (hint n) (finish n)
    (by intro _ impossible; cases impossible)

def assemble (proofs : VC.Proofs) : VerifiedArtifact Assertions.nonnegativeArtifact contract :=
  assembleUsing (fun n => 1 ≤ n + 1) proofs.entry proofs.runtimeAssertion
    (Eq.mpr VC.hint.normalization proofs.hint) proofs.finish

veripy_vcs obligations : VerifiedArtifact Assertions.nonnegativeArtifact contract via assemble where
  entry : VC.entry at 0 vc_kind "entry_compatibility"
  runtimeAssertion : VC.runtimeAssertion at 2 vc_kind "runtime_assertion"
  hint : VC.hint at 20 vc_kind "logical_checkpoint"
  finish : VC.finish at 20 vc_kind "normal_exit"

#veripy_audit VeriPyAsm.Examples.Checkpoints

end VeriPyAsm.Examples.Checkpoints
