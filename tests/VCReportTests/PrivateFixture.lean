import VeriPyAsm.Examples.Checkpoints.VC
import VeriPyAsm.Verification.VC.Discharge

/-! Compiled fixture: VCs that encapsulate predicates in private helpers. An
importing module cannot name those helpers, so reports must not print them.
This module supplies no proofs; its own discovery report is emitted where the
helpers are still local, which must not make the handoff any less portable.
-/

namespace VeriPyAsm.Tests.VCReport.PrivateFixture

open Verification Examples

private def nonnegative (n : Int) : Prop := 0 ≤ n

/-- A transparent private predicate: definitionally `Checkpoints.VC.hint`. -/
def hint : Prop := ∀ n : Int, nonnegative n → 1 ≤ n + 1

private inductive Witness : Prop
  | intro

/-- A private type has no value to unfold; only the VC's name is portable. -/
def finish : Prop := Witness → Checkpoints.VC.finish

structure Proofs : Prop where
  entry : Checkpoints.VC.entry
  runtimeAssertion : Checkpoints.VC.runtimeAssertion
  hint : hint
  finish : finish

def assemble (proofs : Proofs) :
    VerifiedArtifact Assertions.nonnegativeArtifact Checkpoints.contract :=
  Checkpoints.assemble ⟨proofs.entry, proofs.runtimeAssertion, proofs.hint, proofs.finish .intro⟩

veripy_vcs obligations :
    VerifiedArtifact Assertions.nonnegativeArtifact Checkpoints.contract via assemble where
  entry : Checkpoints.VC.entry at 0 vc_kind "entry_compatibility"
  runtimeAssertion : Checkpoints.VC.runtimeAssertion at 2 vc_kind "runtime_assertion"
  hint : hint at 20 vc_kind "logical_checkpoint"
  finish : finish at 20 vc_kind "normal_exit"

#guard_msgs (drop info, all) in
set_option veripy.auto false in
veripy_discover pending from obligations

-- Further shapes, rendered directly rather than through a manifest.
private def Small.{u} {α : Type u} (measure : α → Nat) (value : α) : Prop := measure value ≤ 2
private def both (n : Int) : Prop := nonnegative n ∧ Small Int.natAbs n
def nested : Prop := ∀ n : Int, both n → n ≤ 2

private def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2
def recursive : Prop := ∀ n : Nat, double n = 2 * n

private theorem zeroNonnegative : nonnegative 0 := Int.le_refl 0
private def checked (n : Int) (_ : nonnegative n) : Int := n
def erasedProof : Prop := checked 0 zeroNonnegative = 0
def applied : Prop := nonnegative 3

private opaque secret : Nat
def withOpaque : Prop := secret = secret

private def halvings (n : Nat) : Nat := if n = 0 then 0 else halvings (n / 2) + 1
termination_by n
decreasing_by omega
def wellFounded : Prop := halvings 0 = 0

private structure Pair where
  left : Nat
  right : Nat
def withStructure : Prop := ∀ pair : Pair, pair.left = pair.left

end VeriPyAsm.Tests.VCReport.PrivateFixture
