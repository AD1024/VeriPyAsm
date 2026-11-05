import VeriPyAsm.Verification.Instruction
import VeriPyAsm.Verification.Hoare
import VeriPyAsm.Verification.FusedInstruction

/-! Compositional examples exercise operand order, local updates, truthiness and
both branch edges, preserved exception snapshots, and forbidden VM faults.
The generic programs here make no claim of CPython stack admission. -/

namespace VeriPyAsm.Tests.Instruction

open Semantics Verification
open scoped VeriPyAsm.Verification.Hoare

private def storeLoadReturn : Program := fun pc =>
  if pc = 0 then some (Command.store 1 1)
  else if pc = 1 then some (Command.load false 2 1)
  else if pc = 2 then some Command.ret
  else none

/-- Overwrite one local, reload it, and return it. The other local and the
remaining stack are preserved, and the return is related to both of them. -/
theorem store_load_return (value saved : Value) (rest : List Value) :
    {{ fun s => s = { locals := [some saved, none], stack := value :: rest } }}
      storeLoadReturn
    {{ returns fun result final => result = value ∧
        final.locals = [some saved, some result] ∧ final.stack = rest }} := by
  let afterStore : Frame := { pc := 1, locals := [some saved, some value], stack := rest }
  let beforeReturn : Frame :=
    { pc := 2, locals := [some saved, some value], stack := value :: rest }
  let post : Postcondition := { returned := fun result final => result = value ∧
    final.locals = [some saved, some result] ∧ final.stack = rest }
  have returnRule := (InstructionCorrect.ret post).on_frame
    (initial := beforeReturn) ⟨value, rest, rfl, rfl, rfl, rfl⟩
  have returned : BlockTotalCorrect (step storeLoadReturn) (fun _ => False)
      (fun s => s = beforeReturn) post :=
    returnRule.to_block (by rintro s rfl; rfl) (fun _ _ h => h) (fun _ h => h)
  have loadRule := (InstructionCorrect.load false 2 1
    { post with continues := fun s => s = beforeReturn }).on_frame
    (initial := afterStore) ⟨value, rfl, rfl⟩
  have loaded := loadRule.prepend (by rintro s rfl; rfl) (fun _ _ h => h) returned
  have storeRule := (InstructionCorrect.store 1 1
    { post with continues := fun s => s = afterStore }).on_frame
    (initial := { locals := [some saved, none], stack := value :: rest })
    ⟨by change 1 < 2; decide, value, rest, rfl, rfl⟩
  exact (storeRule.prepend
    (by rintro s rfl; rfl) (fun _ _ h => h) loaded).to_totalCorrect

/-- A noncommutative operation detects reversed stack operands. The alternate
precondition permits TypeError and checks that its frame retains both operands. -/
theorem subtraction_cases (left right : Int) (rest : List Value) :
    InstructionCorrect (Command.binary 7 (Semantics.binary .sub))
      (fun s => s.stack = .int right :: .int left :: rest ∨
        s.stack = .none :: .int left :: rest)
      { continues := fun s => s.pc = 7 ∧ s.stack = .int (left - right) :: rest
        raises := fun exception s =>
          exception = .typeError ∧ s.stack = .none :: .int left :: rest } := by
  apply InstructionCorrect.cases
  · apply (InstructionCorrect.binary 7 (Semantics.binary .sub) _).consequence
      (post := fun _ h => h)
    intro s stack
    exact ⟨.int left, .int right, rest, .int (left - right), stack, rfl, rfl, rfl⟩
  · apply (InstructionCorrect.binary_error 7 (Semantics.binary .sub) _).consequence
      (post := fun _ h => h)
    intro s stack
    exact ⟨.int left, .none, rest, .typeError, stack, rfl, rfl, stack⟩

private def truthBranch : Program := fun pc =>
  if pc = 0 then some (Command.toBool 2)
  else if pc = 2 then some (Command.branch 4 6)
  else none

theorem truthiness_branch (value : Value) (rest : List Value) :
    BlockTotalCorrect (step truthBranch) (fun pc => pc = 4 ∨ pc = 6)
      (fun s => s = { stack := value :: rest })
      { continues := fun s => s.pc = (if value.truthy then 4 else 6) ∧ s.stack = rest } := by
  let post : Postcondition :=
    { continues := fun s => s.pc = (if value.truthy then 4 else 6) ∧ s.stack = rest }
  let middle : Frame := { pc := 2, stack := .bool value.truthy :: rest }
  have branchRule := (InstructionCorrect.branch 4 6 post).on_frame
    (initial := middle) ⟨value.truthy, rest, rfl, rfl, rfl⟩
  have branched : BlockTotalCorrect (step truthBranch) (fun pc => pc = 4 ∨ pc = 6)
      (fun s => s = middle) post := by
    apply branchRule.to_block (by rintro s rfl; rfl) (by rintro s rfl; simp [middle])
    intro s allowed
    change s.pc = (if value.truthy then 4 else 6) ∧ s.stack = rest at allowed
    rw [allowed.1]
    cases value.truthy <;> simp
  have boolRule := (InstructionCorrect.toBool 2
    { post with continues := fun s => s = middle }).on_frame
    (initial := { stack := value :: rest }) ⟨value, rest, rfl, rfl⟩
  exact boolRule.prepend (by rintro s rfl; rfl) (by rintro s rfl; simp) branched

theorem checked_unbound (rest : List Value) :
    TotalCorrect (step (fun _ => some (Command.load true 1 0)))
      (({ raises := fun exception final => exception = .unboundLocalError ∧
          final = { locals := [none], stack := rest } } : Postcondition).toContract
        (fun s => s = { locals := [none], stack := rest })) := by
  let post : Postcondition :=
    { raises := fun exception final => exception = .unboundLocalError ∧
        final = { locals := [none], stack := rest } }
  have rule := (InstructionCorrect.load_unbound 1 0 post).on_frame
    (initial := { locals := [none], stack := rest }) ⟨rfl, rfl, rfl⟩
  exact (rule.to_block (fun _ _ => rfl) (fun _ _ h => h) (fun _ h => h)).to_totalCorrect

private def permissive : Postcondition :=
  { continues := fun _ => True, returned := fun _ _ => True, raises := fun _ _ => True }

theorem unchecked_unbound_rejected :
    ¬ InstructionCorrect (Command.load false 1 0) (fun s => s.locals = [none]) permissive := by
  intro correct
  exact correct { locals := [none] } rfl

theorem store_out_of_bounds_rejected :
    ¬ InstructionCorrect (Command.store 1 0) (fun s => s.locals = []) permissive := by
  intro correct
  exact correct { stack := [.int 4] } rfl

theorem branch_requires_bool :
    ¬ InstructionCorrect (Command.branch 1 2) (fun s => s.stack = [.int 1]) permissive := by
  intro correct
  exact correct { stack := [.int 1] } rfl

theorem return_requires_value :
    ¬ InstructionCorrect Command.ret (fun s => s.stack = []) permissive := by
  intro correct
  exact correct {} rfl

/-- The fused load is atomic and places the second local on top. Both local
values and the prior stack remain symbolic, so swapping the operands is visible. -/
theorem fused_load_order (first second : Value) (rest : List Value) :
    InstructionCorrect (Command.loadPair 9 0 1)
      (fun s => s.locals = [some first, some second] ∧ s.stack = rest)
      { continues := fun s => s.pc = 9 ∧ s.stack = second :: first :: rest ∧
          s.locals = [some first, some second] } := by
  apply (InstructionCorrect.loadPair 9 0 1 _).consequence (post := fun _ h => h)
  rintro s ⟨locals, stack⟩
  exact ⟨first, second, by simp [locals], by simp [locals], rfl, by simp [stack], locals⟩

example (value : Value) (rest : List Value) :
    InstructionCorrect (Command.loadPair 1 0 0)
      (fun s => s = { locals := [some value], stack := rest })
      { continues := fun s => s.stack = value :: value :: rest } :=
  (InstructionCorrect.loadPair 1 0 0 _).on_frame ⟨value, value, rfl, rfl, rfl⟩

theorem fused_second_unbound_rejected :
    ¬ InstructionCorrect (Command.loadPair 1 0 1)
      (fun s => s.locals = [some (.int 1), none]) permissive := by
  intro correct
  exact correct { locals := [some (.int 1), none] } rfl

private def jumpLoop : Program := fun _ => some (Command.jump 2)

private theorem jumpLoop_no_exit {s : Frame} {result : StepResult}
    (execution : BlockExecutes (step jumpLoop) (fun _ => False) s result) : False := by
  induction execution with
  | exit impossible => exact impossible
  | halt _ impossible => cases impossible
  | step _ _ _ ih => exact ih

-- Prepending an instruction preserves partial correctness of a divergent tail.
theorem prepend_divergent : { fun _ => True } jumpLoop { fun _ => False } := by
  have tail : BlockPartialCorrect (step jumpLoop) (fun _ => False) (fun _ => True) {} :=
    fun _ _ _ execution => False.elim (jumpLoop_no_exit execution)
  exact ((InstructionCorrect.jump 2 { continues := fun _ => True }).prepend_partial
    (fun _ _ => rfl) (fun _ _ h => h) tail).to_partialCorrect

#print axioms InstructionCorrect.prepend_partial
#print axioms InstructionCorrect.prepend
#print axioms InstructionCorrect.to_block
#print axioms InstructionCorrect.load
#print axioms InstructionCorrect.store
#print axioms InstructionCorrect.binary
#print axioms InstructionCorrect.binary_error
#print axioms InstructionCorrect.branch
#print axioms InstructionCorrect.ret
#print axioms store_load_return
#print axioms subtraction_cases
#print axioms truthiness_branch
#print axioms checked_unbound
#print axioms InstructionCorrect.loadPair
#print axioms fused_load_order
#print axioms prepend_divergent

end VeriPyAsm.Tests.Instruction
