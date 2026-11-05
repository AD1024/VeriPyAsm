import VeriPyAsm.Target
import VeriPyAsm.Bytecode
import VeriPyAsm.Verification.Artifact
import VeriPyAsm.Verification.VerifiedArtifact
import VeriPyAsm.Verification.AxiomAudit
import VeriPyAsm.Verification.VC.Registry
import VeriPyAsm.Verification.Hoare
import VeriPyAsm.Verification.Instruction
import VeriPyAsm.Verification.FusedInstruction
import VeriPyAsm.Verification.Loop

/-!
# VeriPyAsm

Verification of CPython bytecode in Lean 4.

The library provides scalar bytecode semantics, a pinned baseline decoder,
certified shallow translation, checked stack/ownership admission, and sequential
relational contracts with sound instruction/block/loop rules. VerifiedArtifact
combines admission, entry compatibility, and correctness; exports are axiom-audited.
The triangular example separates closed VCs, conditional assembly, and their
proofs. Exact, axiom-audited VC registration uses `@[veripy_proof Goal]`.
Automatic VC generation remains future work;
see `docs/DESIGN.md` and `docs/PROTOTYPE.md`.
-/

#veripy_audit VeriPyAsm
