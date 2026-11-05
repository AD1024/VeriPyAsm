import VeriPyAsm.Target
import VeriPyAsm.Bytecode
import VeriPyAsm.Verification.Artifact
import VeriPyAsm.Verification.Hoare

/-!
# VeriPyAsm

Verification of CPython bytecode in Lean 4.

The library provides scalar bytecode semantics, a pinned baseline decoder,
certified shallow translation, checked stack admission, and sequential relational
contracts with execution and representation proofs. VC generation and proof
registration remain future work; see `docs/DESIGN.md` and `docs/PROTOTYPE.md`.
-/
