import VeriPyAsm.CPython.V314.Decode

/-! Translation into a shallow Lean program, with a kernel-checked representation
certificate. One command per decoded instruction preserves step boundaries;
block fusion is deferred. The artifact term elaborator lives in Bytecode.lean. -/

namespace VeriPyAsm.Embedding

open Semantics CPython.V314

/-- Translation constructs a function of byte offsets whose leaves are semantic
commands. Evaluation of the resulting program does not fetch an instruction AST. -/
def compileInstructions : List Instruction → Program
  | [] => fun _ => none
  | i :: rest =>
    let command := i.denote
    let tail := compileInstructions rest
    fun pc => if pc = i.offset then some command else tail pc

def compile (code : Code) : Program := compileInstructions code.instructions

theorem compile_fetch (instructions : List Instruction) (pc : Nat) :
    compileInstructions instructions pc = (fetch instructions pc).map Instruction.denote := by
  induction instructions with
  | nil => rfl
  | cons i rest ih =>
    simp only [compileInstructions, fetch]
    split <;> simp_all

/-- Exact one-step correspondence, including returns, exceptions and VM faults. -/
theorem compile_correct (code : Code) : step (compile code) = referenceStep code := by
  funext s
  simp only [step, compile, compile_fetch, referenceStep]
  cases fetch code.instructions s.pc <;> rfl

/-- The same step count gives the same outcome or exhausted continuation. -/
theorem compile_run (code : Code) (fuel : Nat) (frame : Frame) :
    run (step (compile code)) fuel frame = run (referenceStep code) fuel frame := by
  rw [compile_correct]

/-- This package retains the original artifact via its index and connects both
translation stages. Neither extraction fidelity nor CPython's C code is proved. -/
structure Translation (artifact : Artifact) where
  code : Code
  decoded : decode artifact = .ok code
  program : Program
  correct : step program = referenceStep code

/-- The import API for this slice: external tools supply literal `Artifact` data.
Failure is explicit; no default program, `sorry`, or trusted proof is inserted. -/
def translate (artifact : Artifact) : Except DecodeError (Translation artifact) :=
  match h : decode artifact with
  | .error error => .error error
  | .ok code => .ok
      { code, decoded := h, program := compile code, correct := compile_correct code }

end VeriPyAsm.Embedding
