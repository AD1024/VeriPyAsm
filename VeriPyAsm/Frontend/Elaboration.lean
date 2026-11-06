import VeriPyAsm.Verification.VC.Policy

/-! Shared kernel-reducing readers and transactional callers' declaration
publisher. No native evaluation is used as evidence for source certificates. -/

namespace VeriPyAsm.Frontend.Elaboration
open Lean Meta Elab Command Verification.VC

def closed (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars value
  if value.hasFVar || value.hasMVar then throwError "source mapping requires closed inputs"
  match Kernel.whnf (← getEnv) (← getLCtx) value with
  | .ok result => pure result
  | .error error => throwError "source mapping reduction failed: {error.toMessageData (← getOptions)}"

def readNat (value : Expr) : MetaM Nat := do
  let some n ← getNatValue? (← closed value) | throwError "expected a mapping offset"
  return n

def readList {α : Type} (read : Expr → MetaM α) (value : Expr) : MetaM (List α) := do
  let mut result := []
  let mut tail := value
  repeat
    let value ← closed tail
    if value.isAppOfArity ``List.nil 1 then return result.reverse
    unless value.isAppOfArity ``List.cons 3 do throwError "expected a mapping list"
    result := (← read value.getAppArgs[1]!) :: result
    tail := value.getAppArgs[2]!

def readString (value : Expr) : MetaM String := do
  if let some text := getStringValue? (← closed value) then return text
  let chars ← mkAppM ``String.toList #[value]
  let chars ← readList (fun char => do
    return Char.ofNat (← readNat (← mkAppM ``Char.toNat #[char]))) chars
  return String.ofList chars

def publish (name : Name) (type value : Expr) : CoreM Unit := do
  addCheckedDeclaration (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
  enableRealizationsForConst name
  withOptions (fun opts => opts.setBool `Elab.async false) <|
    compileDecls #[name] (logErrors := false)

end VeriPyAsm.Frontend.Elaboration
