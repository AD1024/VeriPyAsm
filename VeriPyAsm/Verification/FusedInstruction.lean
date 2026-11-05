import VeriPyAsm.Semantics.Fused
import VeriPyAsm.Verification.Instruction

/-! Rules for atomic fused commands, retaining the decoder's step boundaries.
The first loop proof needs the pair of loads, shared by borrowing/non-borrowing
opcodes in the scalar profile. Other fused rules can be added independently. -/

namespace VeriPyAsm.Verification.InstructionCorrect

open Semantics

/-- The second loaded value is on top, including when the indices coincide. -/
theorem loadPair (next first second : Nat) (Q : Postcondition) :
    InstructionCorrect (Command.loadPair next first second)
      (fun s => ∃ firstValue secondValue,
        s.locals[first]? = some (some firstValue) ∧
        s.locals[second]? = some (some secondValue) ∧
        Q.continues
          { s with pc := next, stack := secondValue :: firstValue :: s.stack }) Q := by
  rintro s ⟨firstValue, secondValue, firstLookup, secondLookup, post⟩
  simpa only [Command.loadPair, firstLookup, secondLookup, Postcondition.Accepts] using post

end VeriPyAsm.Verification.InstructionCorrect
