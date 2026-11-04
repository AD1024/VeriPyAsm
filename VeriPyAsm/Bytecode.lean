import VeriPyAsm.Admission
import Lean

/-! `bytecode% artifact` elaborates a closed literal artifact into a certified
translation. `admit_bytecode% artifact` additionally checks stack admission.
Both produce kernel-checked certificates. Runtime importers can instead use
`Embedding.translate` and `admit`, respectively. -/

namespace VeriPyAsm

open Lean Meta Elab Term

syntax (name := bytecodeTerm) "bytecode% " term : term
syntax (name := admitBytecodeTerm) "admit_bytecode% " term : term

private def elaborateTranslation (stx : Syntax) : TermElabM (Expr × Expr) := do
  let artifact ← elabTermEnsuringType stx (mkConst ``CPython.V314.Artifact)
  let artifact ← instantiateMVars artifact
  if artifact.hasMVar || artifact.hasFVar then
    throwErrorAt stx "bytecode elaboration requires a closed artifact without metavariables"
  let decoded ← mkAppM ``CPython.V314.decode #[artifact]
  let result ← withTransparency .all <| reduce decoded
  if result.isAppOfArity ``Except.error 3 then
    throwErrorAt stx "bytecode rejected: {result.getAppArgs[2]!}"
  unless result.isAppOfArity ``Except.ok 3 do
    throwErrorAt stx "bytecode elaboration could not reduce the artifact decoder"
  let code := result.getAppArgs[2]!
  let program ← mkAppM ``Embedding.compile #[code]
  let correct ← mkAppM ``Embedding.compile_correct #[code]
  -- `decode artifact = .ok code` is checked by definitional equality.
  let decodedProof ← mkEqRefl decoded
  let translation ← mkAppM ``Embedding.Translation.mk #[code, decodedProof, program, correct]
  return (artifact, translation)

@[term_elab bytecodeTerm] def elabBytecode : TermElab := fun stx _ => do
  return (← elaborateTranslation stx[1]).2

/-- Read only constructor data for diagnostics, without executing compiled code.
Rendering a reduced String directly would expose its internal byte-array term. -/
private def readStackError (error : Expr) : MetaM CPython.V314.Stack.Error := do
  let_expr CPython.V314.Stack.Error.mk offset reason := error
    | throwError "unexpected stack-analysis error representation"
  let nat (e : Expr) : MetaM Nat := do
    let some value ← getNatValue? e | throwError "expected a stack-analysis natural literal"
    pure value
  let reason : CPython.V314.Stack.ErrorReason ← match_expr reason with
    | CPython.V314.Stack.ErrorReason.missingInstruction => pure .missingInstruction
    | CPython.V314.Stack.ErrorReason.underflow required actual => do
      pure (.underflow (← nat required) (← nat actual))
    | CPython.V314.Stack.ErrorReason.invalidReturnHeight actual => do
      pure (.invalidReturnHeight (← nat actual))
    | CPython.V314.Stack.ErrorReason.capacityExceeded height capacity => do
      pure (.capacityExceeded (← nat height) (← nat capacity))
    | CPython.V314.Stack.ErrorReason.inconsistentJoin expected actual => do
      pure (.inconsistentJoin (← nat expected) (← nat actual))
    | CPython.V314.Stack.ErrorReason.analysisLimit => pure .analysisLimit
    | CPython.V314.Stack.ErrorReason.invalidCertificate => pure .invalidCertificate
    | _ => throwError "unrecognized stack-analysis error kind"
  return ⟨← nat offset, reason⟩

@[term_elab admitBytecodeTerm] def elabAdmitBytecode : TermElab := fun stx _ => do
  let (artifact, translation) ← elaborateTranslation stx[1]
  let code ← mkAppM ``Embedding.Translation.code #[translation]
  let capacity ← mkAppM ``CPython.V314.Artifact.stackSize #[artifact]
  let proposed ← mkAppM ``CPython.V314.Stack.infer #[code, capacity]
  let result ← withTransparency .all <| reduce proposed
  if result.isAppOfArity ``Except.error 3 then
    let error ← readStackError result.getAppArgs[2]!
    throwErrorAt stx[1] "stack admission rejected: {error.message}"
  unless result.isAppOfArity ``Except.ok 3 do
    throwErrorAt stx[1] "stack admission could not reduce the analysis"
  let heights := result.getAppArgs[2]!
  let obligation ← mkAppM ``CPython.V314.Stack.Valid #[code, capacity, heights]
  -- The analyzer only proposes a table. Admission separately proves its validity
  -- by reduction in Lean, with no native evaluation or solver trust.
  let proof ← mkDecideProof obligation
  let certificate ← mkAppM ``CPython.V314.Stack.Certificate.mk #[heights, proof]
  mkAppM ``StackAdmitted.mk #[translation, certificate]

end VeriPyAsm
