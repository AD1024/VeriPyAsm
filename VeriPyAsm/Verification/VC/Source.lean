import VeriPyAsm.Verification.VC.Generation

/-! Attach optional diagnostic source spans to existing VC names. This command
changes only manifest metadata: no theorem, normalization, or proof registration.
Bindings must be closed, valid, unique, and refer to actual manifest fields.
All bindings are validated before any metadata is published. -/

namespace VeriPyAsm.Verification.VC
open Lean Meta Elab Command Generation

private def readLocation (expression : Expr) : MetaM SourceLocation := do
  let value ← closedWhnf expression
  let_expr SourceLocation.mk path digest functionName label line column endLine endColumn := value
    | throwError "expected a closed VC.SourceLocation"
  let result : SourceLocation := {
    path := ← readString path, digest := ← readString digest,
    functionName := ← readString functionName, label := ← readString label,
    line := ← readNat line, column := ← readNat column,
    endLine := ← readNat endLine, endColumn := ← readNat endColumn }
  unless !result.path.isEmpty && !result.digest.isEmpty && !result.functionName.isEmpty &&
      !result.label.isEmpty && result.line > 0 && (result.line < result.endLine ||
        (result.line == result.endLine && result.column < result.endColumn)) do
    throwError "invalid VC source identity or span"
  return result

syntax (name := vcSources) "veripy_vc_sources " ident " from " ident : command

@[command_elab vcSources] def elabVCSources : CommandElab := fun stx => do
  let `(veripy_vc_sources $manifestId:ident from $bindingsId:ident) := stx
    | throwUnsupportedSyntax
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo manifestId
  let manifest ← liftCoreM <| getManifest name
  let updated ← liftTermElabM do
    let bindingsName ← realizeGlobalConstNoOverloadWithInfo bindingsId
    discard <| audit bindingsName .checked
    let bindings := mkConst bindingsName
    let expected ← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``String, mkConst ``SourceLocation]]
    unless (← isDefEq (← inferType bindings) expected) do
      throwError "VC source bindings require List (String × VC.SourceLocation)"
    let mut obligations := manifest.obligations
    for binding in ← readList bindings do
      let field ← readString (← mkAppM ``Prod.fst #[binding])
      let some index := obligations.findIdx? (·.field.toString == field)
        | throwError "source binding names unknown VC field {field}"
      if obligations[index]!.source.isSome then
        throwError "duplicate source binding for VC field {field}"
      let location ← readLocation (← mkAppM ``Prod.snd #[binding])
      obligations := obligations.modify index (fun obligation => { obligation with source := some location })
    return { manifest with obligations }
  modifyEnv fun env => manifests.addEntry env updated

end VeriPyAsm.Verification.VC
