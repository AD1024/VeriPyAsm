import VeriPyAsm.Verification.VC.Registry
import VeriPyAsm.Verification.VerifiedArtifact

/-! A manifest connects named, closed VCs to a conditional assembly function.
It contains no proofs and performs no automatic VC generation. The assembly must
take one unparameterized proof structure and return a `VerifiedArtifact`.
Every field is listed exactly once, in constructor order, with bytecode metadata.
-/

namespace VeriPyAsm.Verification.VC

open Lean Meta Elab Command

structure Obligation where
  field : Name
  goal : Name
  offset : Nat
  kind : String
  deriving Inhabited

structure Manifest where
  name : Name
  origin : Name
  resultType : Expr
  assembly : Name
  constructor : Name
  obligations : Array Obligation
  deriving Inhabited

initialize manifests : SimplePersistentEnvExtension Manifest (NameMap Manifest) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state manifest => state.insert manifest.name manifest
    addImportedFn := fun modules => modules.foldl
      (fun state entries => entries.foldl (fun state entry => state.insert entry.name entry) state) {}
  }

def getManifest (name : Name) : CoreM Manifest := do
  let some manifest := manifests.getState (← getEnv) |>.find? name
    | throwError "unknown VC manifest {name}"
  return manifest

/-- A marker declaration lets Lean resolve manifest names normally across
namespaces and imports; the extension retains the elaborated metadata. -/
def manifestMarker : Unit := ()

syntax vcEntry := ident " : " ident " at " num " vc_kind " str
syntax (name := manifestCommand) "veripy_vcs " ident " : " term " via " ident
  " where " ppLine (colGt vcEntry ppLine)+ : command

@[command_elab manifestCommand] def elabManifest : CommandElab := fun stx => do
  let `(veripy_vcs $id:ident : $result:term via $assemblyId:ident where $entries:vcEntry*) := stx
    | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ id.getId
  if (← getEnv).contains name then throwErrorAt id "declaration already exists: {name}"
  let assembly ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo assemblyId
  let (resultType, constructor, fields) ← liftTermElabM do
    let resultType ← Term.elabType result
    Term.synthesizeSyntheticMVarsNoPostponing
    let resultType ← instantiateMVars resultType
    unless !resultType.hasMVar && !resultType.hasFVar do
      throwError "VC assembly result must be closed"
    let resultHead ← whnf resultType
    unless resultHead.isAppOf ``VerifiedArtifact do
      throwError "VC assembly must produce a VerifiedArtifact package"
    let info ← getConstInfo assembly
    unless info.levelParams.isEmpty do throwError "VC assembly must be closed without universe parameters"
    let .forallE _ bundle resultBody _ ← whnf info.type
      | throwError "VC assembly must take exactly one proof structure"
    if resultBody.hasLooseBVars || !(← isDefEq resultBody resultType) then
      throwError "VC assembly result does not match the declared VerifiedArtifact"
    let .const bundleName [] := bundle
      | throwError "VC assembly requires an unparameterized proof structure"
    unless (← isProp bundle) && (getStructureInfo? (← getEnv) bundleName).isSome do
      throwError "VC assembly input must be a proof structure"
    let constructor := getStructureCtor (← getEnv) bundleName
    unless constructor.numParams == 0 do throwError "parameterized VC structures are not supported"
    let fields := getStructureFields (← getEnv) bundleName
    unless fields.size == entries.size do throwError "list every VC structure field exactly once"
    let mut type := constructor.type
    for entry in entries, field in fields do
      let `(vcEntry| $fieldId:ident : $goalId:ident at $_offset:num vc_kind $_kind:str) := entry
        | throwUnsupportedSyntax
      unless fieldId.getId == field do
        throwErrorAt fieldId "expected VC field {field}; list fields in constructor order"
      let goal ← realizeGlobalConstNoOverloadWithInfo goalId
      let goalExpr ← VC.goalExpr goal
      let .forallE _ fieldType rest _ := type
        | throwError "unexpected VC structure constructor"
      -- This is only a manifest shape check; final assembly is kernel checked.
      unless !fieldType.hasLooseBVars && (← isDefEq fieldType goalExpr) do
        throwErrorAt goalId "VC {goal} does not match structure field {field}"
      type := rest
    return (resultType, constructor.name, fields)
  let mut obligations := #[]
  for entry in entries, field in fields do
    let `(vcEntry| $_fieldId:ident : $goalId:ident at $offset:num vc_kind $kindText:str) := entry
      | throwUnsupportedSyntax
    let goal ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo goalId
    obligations := obligations.push { field, goal, offset := offset.getNat, kind := kindText.getString }
  let manifest : Manifest := {
    name, origin := ← getMainModule, resultType, assembly, constructor, obligations }
  liftCoreM <| addCheckedDeclaration (.defnDecl {
    name, levelParams := [], type := mkConst ``Unit, value := mkConst ``manifestMarker,
    hints := .abbrev, safety := .safe })
  modifyEnv fun env => manifests.addEntry env manifest

end VeriPyAsm.Verification.VC
