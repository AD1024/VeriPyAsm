import VeriPyAsm.Target
import VeriPyAsm.Bytecode
import VeriPyAsm.Verification.Artifact
import VeriPyAsm.Verification.Hoare
import VeriPyAsm.Verification.Instruction
import VeriPyAsm.Verification.FusedInstruction
import VeriPyAsm.Verification.Loop

/-!
# VeriPyAsm

Verification of CPython bytecode in Lean 4.

The library provides scalar bytecode semantics, a pinned baseline decoder,
certified shallow translation, checked stack admission, and sequential relational
contracts with sound instruction/block/loop rules and representation proofs.
The triangular example separates closed VCs, conditional assembly, and their
proofs. Automatic VC generation and proof registration remain future work;
see `docs/DESIGN.md` and `docs/PROTOTYPE.md`.
-/
