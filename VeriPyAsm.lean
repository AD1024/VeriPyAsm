import VeriPyAsm.Target
import VeriPyAsm.Bytecode

/-!
# VeriPyAsm

Verification of CPython bytecode in Lean 4.

The library provides scalar bytecode semantics, a pinned baseline decoder,
certified shallow translation, and checked stack admission with soundness proofs.
Specifications and VC generation remain future work; see `docs/DESIGN.md` and
`docs/PROTOTYPE.md`.
-/
