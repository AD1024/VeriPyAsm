import VeriPyAsm.Target
import VeriPyAsm.Bytecode

/-!
# VeriPyAsm

Verification of CPython bytecode in Lean 4.

The first slice provides scalar bytecode semantics, a pinned baseline decoder,
and certified translation into shallow semantic commands. Specifications and VC
generation remain future work; see `docs/DESIGN.md` and `docs/PROTOTYPE.md`.
-/
