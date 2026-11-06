import VeriPyAsm.Examples.Triangular.Specification
import VeriPyAsm.Verification.FusedInstruction
import VeriPyAsm.Verification.Loop

/-! Symbolic summaries of the imported artifact's entry, body, test, and return.
Each instruction rule checks lookup in the certified translation. Arithmetic
invariants and termination arguments are deliberately kept out of these summaries.
In this artifact the true branch at 14 goes directly to 20, skipping NOT_TAKEN. -/

namespace VeriPyAsm.Examples.Triangular

open Semantics Verification

def cuts (pc : Nat) : Prop := pc = 6 ∨ pc = 58

theorem entry (n : Int) :
    BlockTotalCorrect (step triangular.translation.program) (fun pc => pc = 6)
      (fun s => s = { locals := [some (.int n), none] })
      { continues := fun s => s = frame 6 n 0 } := by
  let post : Postcondition := { continues := fun s => s = frame 6 n 0 }
  have storeRule := (InstructionCorrect.store 6 1 post).on_frame
    (initial := { pc := 4, locals := [some (.int n), none], stack := [.int 0] })
    ⟨by change 1 < 2; decide, .int 0, [], rfl, rfl⟩
  have stored : BlockTotalCorrect (step triangular.translation.program) (fun pc => pc = 6)
      (fun s => s = { pc := 4, locals := [some (.int n), none], stack := [.int 0] }) post :=
    storeRule.to_block (by rintro s rfl; rfl) (by rintro s rfl; simp)
      (by rintro s rfl; rfl)
  have pushRule := (InstructionCorrect.push 4 (.int 0)
    { post with continues := fun s =>
        s = { pc := 4, locals := [some (.int n), none], stack := [.int 0] } }).on_frame
    (initial := { pc := 2, locals := [some (.int n), none] }) rfl
  have pushed := pushRule.prepend (by rintro s rfl; rfl) (by rintro s rfl; simp) stored
  have resumeRule := (InstructionCorrect.jump 2
    { post with continues := fun s => s = { pc := 2, locals := [some (.int n), none] } }).on_frame
    (initial := { locals := [some (.int n), none] }) rfl
  exact resumeRule.prepend (by rintro s rfl; rfl) (by rintro s rfl; simp) pushed

/-- The body updates both locals and restores the empty stack at the header.
It is valid for all integers; nonnegativity belongs to the invariant proof. -/
theorem body (n sum : Int) :
    BlockTotalCorrect (step triangular.translation.program) cuts
      (fun s => s = frame 20 n sum)
      { continues := fun s => s = frame 6 (n - 1) (sum + n) } := by
  let post : Postcondition := { continues := fun s => s = frame 6 (n - 1) (sum + n) }
  have jumpRule := (InstructionCorrect.jump 6 post).on_frame
    (initial := frame 54 (n - 1) (sum + n)) rfl
  have jumped : BlockTotalCorrect (step triangular.translation.program) cuts
      (fun s => s = frame 54 (n - 1) (sum + n)) post :=
    jumpRule.to_block (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame])
      (by rintro s rfl; exact Or.inl rfl)
  have storeN := (InstructionCorrect.store 54 0
    { post with continues := fun s => s = frame 54 (n - 1) (sum + n) }).on_frame
    (initial := frame 52 n (sum + n) [.int (n - 1)])
    ⟨by change 0 < 2; decide, .int (n - 1), [], rfl, rfl⟩
  have storedN := storeN.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) jumped
  have subtract := (InstructionCorrect.binary 52 (Semantics.binary .sub)
    { post with continues := fun s => s = frame 52 n (sum + n) [.int (n - 1)] }).on_frame
    (initial := frame 40 n (sum + n) [.int 1, .int n])
    ⟨.int n, .int 1, [], .int (n - 1), rfl, rfl, rfl⟩
  have subtracted := subtract.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) storedN
  have pushOne := (InstructionCorrect.push 40 (.int 1)
    { post with continues := fun s => s = frame 40 n (sum + n) [.int 1, .int n] }).on_frame
    (initial := frame 38 n (sum + n) [.int n]) rfl
  have pushed := pushOne.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) subtracted
  have loadN := (InstructionCorrect.load false 38 0
    { post with continues := fun s => s = frame 38 n (sum + n) [.int n] }).on_frame
    (initial := frame 36 n (sum + n)) ⟨.int n, rfl, rfl⟩
  have loadedN := loadN.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) pushed
  have storeSum := (InstructionCorrect.store 36 1
    { post with continues := fun s => s = frame 36 n (sum + n) }).on_frame
    (initial := frame 34 n sum [.int (sum + n)])
    ⟨by change 1 < 2; decide, .int (sum + n), [], rfl, rfl⟩
  have storedSum := storeSum.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) loadedN
  have add := (InstructionCorrect.binary 34 (Semantics.binary .add)
    { post with continues := fun s => s = frame 34 n sum [.int (sum + n)] }).on_frame
    (initial := frame 22 n sum [.int n, .int sum])
    ⟨.int sum, .int n, [], .int (sum + n), rfl, rfl, rfl⟩
  have added := add.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) storedSum
  have loadBoth := (InstructionCorrect.loadPair 22 1 0
    { post with continues := fun s => s = frame 22 n sum [.int n, .int sum] }).on_frame
    (initial := frame 20 n sum) ⟨.int sum, .int n, rfl, rfl, rfl⟩
  exact loadBoth.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) added

def iterationPost (n sum : Int) : Postcondition :=
  { continues := fun s =>
      (0 < n ∧ s = frame 6 (n - 1) (sum + n)) ∨ (n ≤ 0 ∧ s = frame 58 n sum) }

/-- A complete, nonempty iteration includes the test and either the body/back
edge or the exit edge. Both control-flow alternatives are proved symbolically. -/
theorem iteration (n sum : Int) :
    IterationTotalCorrect (step triangular.translation.program) cuts
      (fun s => s = frame 6 n sum) (iterationPost n sum) := by
  let post := iterationPost n sum
  have branchTail : BlockTotalCorrect (step triangular.translation.program) cuts
      (fun s => s = frame (if 0 < n then 20 else 58) n sum) post := by
    by_cases positive : 0 < n
    · simp only [positive, ↓reduceIte]
      apply (body n sum).consequence (fun _ h => h)
      intro result allowed
      cases result with
      | next s => exact Or.inl ⟨positive, allowed⟩
      | halted outcome => cases outcome <;> exact False.elim allowed
    · simp only [positive, ↓reduceIte]
      apply BlockTotalCorrect.exit
      · rintro s rfl
        exact Or.inr rfl
      · rintro s rfl
        exact Or.inr ⟨by omega, rfl⟩
  have branchRule := (InstructionCorrect.branch 20 58
    { post with continues := fun s => s = frame (if 0 < n then 20 else 58) n sum }).on_frame
    (initial := frame 14 n sum [.bool (decide (0 < n))])
    ⟨decide (0 < n), [], rfl, by by_cases h : 0 < n <;> simp [h, frame]⟩
  have branched := branchRule.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) branchTail
  have compareRule := (InstructionCorrect.binary 14 (Semantics.compare .gt)
    { post with continues := fun s => s = frame 14 n sum [.bool (decide (0 < n))] }).on_frame
    (initial := frame 10 n sum [.int 0, .int n])
    ⟨.int n, .int 0, [], .bool (decide (0 < n)), rfl, rfl, rfl⟩
  have compared := compareRule.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) branched
  have pushZero := (InstructionCorrect.push 10 (.int 0)
    { post with continues := fun s => s = frame 10 n sum [.int 0, .int n] }).on_frame
    (initial := frame 8 n sum [.int n]) rfl
  have pushed := pushZero.prepend
    (by rintro s rfl; rfl) (by rintro s rfl; simp [cuts, frame]) compared
  have loadN := (InstructionCorrect.load false 8 0
    { post with continues := fun s => s = frame 8 n sum [.int n] }).on_frame
    (initial := frame 6 n sum) ⟨.int n, rfl, rfl⟩
  exact loadN.start_iteration (by rintro s rfl; rfl) pushed

theorem finish (n sum : Int) :
    BlockTotalCorrect (step triangular.translation.program) (fun _ => False)
      (fun s => s = frame 58 n sum)
      { returned := fun value final => value = .int sum ∧ final = frame 60 n sum } := by
  let post : Postcondition :=
    { returned := fun value final => value = .int sum ∧ final = frame 60 n sum }
  have returnRule := (InstructionCorrect.ret post).on_frame
    (initial := frame 60 n sum [.int sum]) ⟨.int sum, [], rfl, rfl, rfl⟩
  have returned : BlockTotalCorrect (step triangular.translation.program) (fun _ => False)
      (fun s => s = frame 60 n sum [.int sum]) post :=
    returnRule.to_block (by rintro s rfl; rfl) (fun _ _ h => h) (fun _ h => h)
  have loadSum := (InstructionCorrect.load false 60 1
    { post with continues := fun s => s = frame 60 n sum [.int sum] }).on_frame
    (initial := frame 58 n sum) ⟨.int sum, rfl, rfl⟩
  exact loadSum.prepend (by rintro s rfl; rfl) (fun _ _ h => h) returned

end VeriPyAsm.Examples.Triangular
