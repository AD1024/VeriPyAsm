import VeriPyAsm.Examples.Triangular

/-! Lifetime regressions: crafted external bytes, all fused local operations,
joins/back edges, and adversarial certificate tables. Unsafe bytes are tested
against the checker, never executed in CPython by the regression suite. -/

namespace VeriPyAsm.Tests.Ownership

open Semantics CPython.V314 Verification
open CPython.V314.Ownership

/-- Review reproduction: retain a borrow of 1001 while overwriting its owner. -/
def borrowedArtifact : Artifact :=
  { build := "CPython 3.14.4 ownership regression"
    name := "outstanding_borrow"
    code := [128, 0, 82, 0, 94, 1, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      112, 0, 86, 0, 94, 0, 112, 0, 82, 0, 94, 2, 44, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 112, 0, 35, 0]
    constants := [.int 1000]
    argCount := 0
    localNames := ["x"]
    stackSize := 3 }

def stackOnly : StackAdmitted borrowedArtifact := admit_stack_bytecode% borrowedArtifact

-- The value-level theorem remains true. It is insufficient for runtime admission.
theorem model_result : run (step stackOnly.translation.program) 14 { locals := [none] } =
    .halted (.returned (.int 1001) { pc := 44, locals := [some (.int 1002)] }) := by
  decide +kernel

private def rejection (artifact : Artifact) : Option AdmissionError :=
  match admit artifact with
  | .ok _ => none
  | .error error => some error

example : rejection borrowedArtifact =
    some (.ownership ⟨24, .violation (.overwriteBorrowed 0)⟩) := by decide +kernel

/-- error: ownership admission rejected: byte offset 24: cannot overwrite local 0 while its borrow is live -/
#guard_msgs in
#check admit_bytecode% borrowedArtifact

def ownedArtifact : Artifact := { borrowedArtifact with code := borrowedArtifact.code.set 20 84 }
def owned : Admitted ownedArtifact := admit_bytecode% ownedArtifact

example : rejection ownedArtifact = none := by decide +kernel
example : run (step owned.translation.program) 14 { locals := [none] } =
    .halted (.returned (.int 1001) { pc := 44, locals := [some (.int 1002)] }) := by
  decide +kernel

-- A supported borrow may be consumed before the owner's next assignment.
example : transfer (.binary .add) [.owned, .borrowed 0] = .ok [.owned] := rfl
example : transfer (.storeFast 0) [.owned] = .ok [] := rfl
example : transfer .returnValue [.borrowed 0] = .ok [] := rfl
example : transfer .toBool [.borrowed 0] = .ok [.owned] := rfl

-- Neither storing a borrow nor overwriting a supporting local is permitted.
example : transfer (.storeFast 1) [.borrowed 0] = .error (.storeBorrow 0 1) := rfl
example : transfer (.storeFast 0) [.owned, .borrowed 0] =
    .error (.overwriteBorrowed 0) := by rfl
example : transfer (.storeFast 1) [.owned, .borrowed 0] = .ok [.borrowed 0] := by rfl

-- Packed loads preserve the second-on-top ordering, including equal indices.
example : transfer (.loadFastBorrowLoadFastBorrow 0 1) [] =
    .ok [.borrowed 1, .borrowed 0] := rfl
example : transfer (.loadFastBorrowLoadFastBorrow 0 0) [] =
    .ok [.borrowed 0, .borrowed 0] := rfl
example : transfer (.loadFastLoadFast 0 1) [] = .ok [.owned, .owned] := rfl

-- Fusions must check intermediate writes, even if their final stack is safe.
example : transfer (.storeFastLoadFast 0 1) [.owned, .borrowed 0] =
    .error (.overwriteBorrowed 0) := by rfl
example : transfer (.storeFastLoadFast 1 0) [.borrowed 0] =
    .error (.storeBorrow 0 1) := rfl
example : transfer (.storeFastLoadFast 0 0) [.owned] = .ok [.owned] := rfl
example : transfer (.storeFastStoreFast 0 1) [.owned, .borrowed 0] =
    .error (.overwriteBorrowed 0) := by rfl
example : transfer (.storeFastStoreFast 0 1) [.owned, .borrowed 2] =
    .error (.storeBorrow 2 1) := by rfl
example : transfer (.storeFastStoreFast 0 1) [.owned, .owned, .borrowed 1] =
    .error (.overwriteBorrowed 1) := by rfl
example : transfer (.storeFastStoreFast 0 0) [.owned, .owned] = .ok [] := by rfl

private def instruction (offset next : Nat) (op : Op) : Instruction :=
  { offset, next, opcode := 0, arg := 0, op }

private def stableLoop : Code := ⟨[
  instruction 0 2 (.loadFastBorrow 0), instruction 2 4 (.jump 2)]⟩

example : (infer stableLoop).isOk = true := by rfl

private def conflictingJoin : Code := ⟨[
  instruction 0 2 (.loadSmallInt 1), instruction 2 4 (.popJumpIfTrue 4 8),
  instruction 4 6 (.loadFastBorrow 0), instruction 6 8 (.jump 12),
  instruction 8 10 (.loadFast 0), instruction 10 12 (.jump 12),
  instruction 12 14 .returnValue]⟩

example : infer conflictingJoin = .error ⟨12, .inconsistentJoin⟩ := by rfl

-- An invalidating write on either branch is checked even if the branch's value
-- semantics could make that edge unreachable for a particular input.
private def branchHazard : Code := ⟨[
  instruction 0 2 (.loadFastBorrow 0), instruction 2 4 (.loadSmallInt 1),
  instruction 4 6 (.popJumpIfTrue 6 10), instruction 6 8 .returnValue,
  instruction 10 12 (.loadSmallInt 0), instruction 12 14 (.storeFast 0),
  instruction 14 16 .returnValue]⟩

example : infer branchHazard = .error ⟨12, .violation (.overwriteBorrowed 0)⟩ := by rfl

private def loopHazard : Code := ⟨[
  instruction 0 2 (.loadFastBorrow 0), instruction 2 4 (.loadSmallInt 0),
  instruction 4 6 (.storeFast 0), instruction 6 8 (.jump 2)]⟩

example : infer loopHazard = .error ⟨4, .violation (.overwriteBorrowed 0)⟩ := by rfl

-- Forge the successor's borrow as owned, omit an edge, or duplicate an offset.
-- The independent checker rejects each proposal, regardless of the analyzer.
example : (check stableLoop [(0, []), (2, [.owned])]).isNone = true := by rfl
example : (check stableLoop [(0, [])]).isNone = true := by rfl
example : (check stableLoop [(0, []), (0, []), (2, [.borrowed 0])]).isNone = true := by rfl
example : (check loopHazard [(0, []), (2, [.borrowed 0]),
    (4, [.owned, .borrowed 0]), (6, [.borrowed 0])]).isNone = true := by rfl

example : True := by
  fail_if_success
    have _ : CPython.V314.Ownership.Certificate stackOnly.translation.code := owned.ownership
  trivial

#print axioms store_safe
#print axioms Certificate.tracks_reaches
#print axioms Admitted.reachable_ownership
#print axioms owned

end VeriPyAsm.Tests.Ownership
