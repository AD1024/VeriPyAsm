import VeriPyAsm.Embedding
import Lean

/-! `bytecode% artifact` elaborates a closed literal artifact into a certified
translation. The decoder is reduced in Lean; the produced certificate is checked
by the kernel. Runtime importers can instead use `Embedding.translate`. -/

namespace VeriPyAsm

open Lean Meta Elab Term

syntax (name := bytecodeTerm) "bytecode% " term : term

@[term_elab bytecodeTerm] def elabBytecode : TermElab := fun stx _ => do
  let artifact ← elabTermEnsuringType stx[1] (mkConst ``CPython.V314.Artifact)
  let artifact ← instantiateMVars artifact
  if artifact.hasMVar || artifact.hasFVar then
    throwErrorAt stx[1] "bytecode% requires a closed artifact without metavariables"
  let decoded ← mkAppM ``CPython.V314.decode #[artifact]
  let result ← withTransparency .all <| reduce decoded
  if result.isAppOfArity ``Except.error 3 then
    throwErrorAt stx[1] "bytecode rejected: {result.getAppArgs[2]!}"
  unless result.isAppOfArity ``Except.ok 3 do
    throwErrorAt stx[1] "bytecode% could not reduce the artifact decoder"
  let code := result.getAppArgs[2]!
  let program ← mkAppM ``Embedding.compile #[code]
  let correct ← mkAppM ``Embedding.compile_correct #[code]
  -- `decode artifact = .ok code` is checked by definitional equality.
  let decodedProof ← mkEqRefl decoded
  mkAppM ``Embedding.Translation.mk #[code, decodedProof, program, correct]

end VeriPyAsm
