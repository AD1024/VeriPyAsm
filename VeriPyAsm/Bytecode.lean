import VeriPyAsm.Admission
import Lean

/-! `bytecode% artifact` elaborates a closed literal artifact into a certified
translation. `admit_bytecode% artifact` additionally checks stack and ownership
admission; `admit_stack_bytecode%` exposes the lower-level stack-only interface.
Both produce kernel-checked certificates. Runtime importers can instead use
`Embedding.translate` and `admit`, respectively. -/

namespace VeriPyAsm

open Lean Meta Elab Term

syntax (name := bytecodeTerm) "bytecode% " term : term
syntax (name := admitBytecodeTerm) "admit_bytecode% " term : term
syntax (name := admitStackBytecodeTerm) "admit_stack_bytecode% " term : term

/-- Reduce closed computations using the kernel. Meta-level reduction repeatedly
unfolds decoder continuations and scales poorly even for small loops. This only
selects the result constructor; generated certificates are still kernel checked. -/
private def reduceClosed (term : Expr) : MetaM Expr := do
  let term ← instantiateMVars term
  if term.hasMVar || term.hasFVar then
    throwError "bytecode reduction requires a closed expression without metavariables"
  match Kernel.whnf (← getEnv) (← getLCtx) term with
  | .ok result => pure result
  | .error error => throwError "bytecode reduction failed: {error.toMessageData (← getOptions)}"

private def elaborateTranslation (stx : Syntax) : TermElabM (Expr × Expr) := do
  let artifact ← elabTermEnsuringType stx (mkConst ``CPython.V314.Artifact)
  let artifact ← instantiateMVars artifact
  if artifact.hasMVar || artifact.hasFVar then
    throwErrorAt stx "bytecode elaboration requires a closed artifact without metavariables"
  let decoded ← mkAppM ``CPython.V314.decode #[artifact]
  let result ← reduceClosed decoded
  if result.isAppOfArity ``Except.error 3 then
    -- Normalize only the diagnostic payload, not the successful instruction data.
    let error ← withTransparency .all <| reduce result.getAppArgs[2]!
    throwErrorAt stx "bytecode rejected: {error}"
  unless result.isAppOfArity ``Except.ok 3 do
    throwErrorAt stx "bytecode elaboration could not reduce the artifact decoder"
  let code := result.getAppArgs[2]!
  let program ← mkAppM ``Embedding.compile #[code]
  let correct ← mkAppM ``Embedding.compile_correct #[code]
  -- `decode artifact = .ok code` is checked by definitional equality.
  let decodedProof ← mkEqRefl decoded
  -- All arguments are known. Avoid repeating decoder reduction in Meta's
  -- implicit-argument unification; the kernel checks this constructor application,
  -- including the definitional equality required by `decodedProof`.
  let translation := mkAppN (mkConst ``Embedding.Translation.mk)
    #[artifact, code, decodedProof, program, correct]
  return (artifact, translation)

@[term_elab bytecodeTerm] def elabBytecode : TermElab := fun stx _ => do
  return (← elaborateTranslation stx[1]).2

/-- Read only constructor data for diagnostics, without executing compiled code.
Rendering a reduced String directly would expose its internal byte-array term. -/
private def readStackError (error : Expr) : MetaM CPython.V314.Stack.Error := do
  let error ← withTransparency .all <| reduce error
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

private def elaborateStack (stx : Syntax) : TermElabM Expr := do
  let (artifact, translation) ← elaborateTranslation stx
  let code ← mkAppM ``Embedding.Translation.code #[translation]
  let capacity ← mkAppM ``CPython.V314.Artifact.stackSize #[artifact]
  let proposed ← mkAppM ``CPython.V314.Stack.infer #[code, capacity]
  let result ← reduceClosed proposed
  if result.isAppOfArity ``Except.error 3 then
    let error ← readStackError result.getAppArgs[2]!
    throwErrorAt stx "stack admission rejected: {error.message}"
  unless result.isAppOfArity ``Except.ok 3 do
    throwErrorAt stx "stack admission could not reduce the analysis"
  let heights := result.getAppArgs[2]!
  let obligation ← mkAppM ``CPython.V314.Stack.Valid #[code, capacity, heights]
  -- The analyzer only proposes a table. Admission separately proves its validity
  -- by reduction in Lean, with no native evaluation or solver trust.
  let proof ← mkDecideProof obligation
  let certificate ← mkAppM ``CPython.V314.Stack.Certificate.mk #[heights, proof]
  mkAppM ``StackAdmitted.mk #[translation, certificate]

@[term_elab admitStackBytecodeTerm] def elabAdmitStackBytecode : TermElab := fun stx _ =>
  elaborateStack stx[1]

private def readOwnershipError (error : Expr) : MetaM CPython.V314.Ownership.Error := do
  let error ← withTransparency .all <| reduce error
  let_expr CPython.V314.Ownership.Error.mk offset reason := error
    | throwError "unexpected ownership-analysis error representation"
  let nat (e : Expr) : MetaM Nat := do
    let some value ← getNatValue? e | throwError "expected an ownership-analysis natural literal"
    pure value
  let reason : CPython.V314.Ownership.ErrorReason ← match_expr reason with
    | CPython.V314.Ownership.ErrorReason.missingInstruction => pure .missingInstruction
    | CPython.V314.Ownership.ErrorReason.inconsistentJoin => pure .inconsistentJoin
    | CPython.V314.Ownership.ErrorReason.analysisLimit => pure .analysisLimit
    | CPython.V314.Ownership.ErrorReason.invalidCertificate => pure .invalidCertificate
    | CPython.V314.Ownership.ErrorReason.violation violation => do
      let violation ← match_expr violation with
        | CPython.V314.Ownership.Violation.underflow => pure .underflow
        | CPython.V314.Ownership.Violation.storeBorrow source destination =>
          pure (.storeBorrow (← nat source) (← nat destination))
        | CPython.V314.Ownership.Violation.overwriteBorrowed index =>
          pure (.overwriteBorrowed (← nat index))
        | _ => throwError "unrecognized ownership violation"
      pure (.violation violation)
    | _ => throwError "unrecognized ownership-analysis error kind"
  return ⟨← nat offset, reason⟩

@[term_elab admitBytecodeTerm] def elabAdmitBytecode : TermElab := fun stx expectedType? => do
  let structural ← elaborateStack stx[1]
  let translation ← mkAppM ``StackAdmitted.translation #[structural]
  let code ← mkAppM ``Embedding.Translation.code #[translation]
  let proposed ← mkAppM ``CPython.V314.Ownership.infer #[code]
  let result ← reduceClosed proposed
  if result.isAppOfArity ``Except.error 3 then
    let error ← readOwnershipError result.getAppArgs[2]!
    throwErrorAt stx[1] "ownership admission rejected: {error.message}"
  unless result.isAppOfArity ``Except.ok 3 do
    throwErrorAt stx[1] "ownership admission could not reduce the analysis"
  let table := result.getAppArgs[2]!
  let obligation ← mkAppM ``CPython.V314.Ownership.Valid #[code, table]
  let proof ← mkDecideProof obligation
  let certificate ← mkAppM ``CPython.V314.Ownership.Certificate.mk #[table, proof]
  let admitted ← mkAppM ``Admitted.mk #[structural, certificate]
  ensureHasType expectedType? admitted

end VeriPyAsm
