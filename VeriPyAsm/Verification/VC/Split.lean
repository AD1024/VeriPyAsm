import VeriPyAsm.Verification.VC.Generation

/-! Proof-producing partition of a normalized scoped WP. Only positive
conjunctions, universal quantifiers, and conditional branches are distributed.
Antecedents are retained verbatim; no other obligation is assumed. Every
partition carries a reconstruction term, checked again when it is published.
Unknown logical forms containing a boundary are rejected, never dropped. -/

namespace VeriPyAsm.Verification.VC.Generation
open Lean Meta

private theorem ite_of_branches (condition a b : Prop) [Decidable condition]
    (valid : (condition → a) ∧ (¬ condition → b)) : ite condition a b := by
  split <;> rename_i h
  · exact valid.1 h
  · exact valid.2 h

private theorem dite_of_branches (condition : Prop) [Decidable condition]
    (a : condition → Prop) (b : ¬ condition → Prop)
    (valid : (∀ h, a h) ∧ (∀ h, b h)) : dite condition a b := by
  split <;> rename_i h
  · exact valid.1 h
  · exact valid.2 h

structure PartKey where
  header : Nat := 0
  kind : String := "execution_safety"
  deriving BEq, Inhabited

def PartKey.field (key : PartKey) : Name :=
  if key.kind == "execution_safety" then `safety
  else Name.mkSimple s!"loop_{key.header}_{key.kind}"

private def requirementKey (header kind : Expr) : MetaM PartKey := do
  let kind ← closedWhnf kind
  let text ← match kind.constName? with
    | some ``RequirementKind.initialization => pure "init"
    | some ``RequirementKind.preservation => pure "preservation"
    | some ``RequirementKind.ranking => pure "ranking"
    | some ``RequirementKind.exit => pure "exit"
    | _ => throwError "unknown scoped requirement kind"
  return { header := ← readNat header, kind := text }

structure Partition where
  parts : Array (PartKey × Expr)
  /-- A lambda taking one proof per part, in order, and recovering the input. -/
  reconstruct : Expr
  deriving Inhabited

private def hasRequirement (expression : Expr) : Bool :=
  expression.getUsedConstants.contains ``requirement

private def withProofs {α : Type} [Inhabited α] (parts : Array (PartKey × Expr))
    (action : Array Expr → MetaM α) : MetaM α :=
  withLocalDeclsD (parts.map fun (key, goal) => (key.field, fun _ => pure goal)) action

/-- This algorithm is untrusted. Its output is a normal Lean proof term; a
missing case or incorrect projection cannot pass the kernel assembly check. -/
partial def partition (expression : Expr) (owner : PartKey := {}) : MetaM Partition := do
  if expression.isAppOfArity ``requirement 3 then
    let args := expression.getAppArgs
    return ← partition args[2]! (← requirementKey args[0]! args[1]!)
  if expression.isConstOf ``True then return ⟨#[], mkConst ``True.intro⟩
  if let .forallE name type body info := expression then
    if hasRequirement type then throwError "scoped requirement occurs in a dependent/negative position"
    return ← withLocalDecl name info type fun binder => do
      let child ← partition (body.instantiate1 binder) owner
      let parts ← child.parts.mapM fun (key, goal) => do
        return (key, ← mkForallFVars #[binder] goal)
      withProofs parts fun proofs => do
        let proof := mkAppN child.reconstruct (proofs.map (mkApp · binder))
        return ⟨parts, ← mkLambdaFVars proofs (← mkLambdaFVars #[binder] proof)⟩
  if expression.isAppOfArity ``And 2 then
    let left ← partition expression.getAppArgs[0]! owner
    let right ← partition expression.getAppArgs[1]! owner
    let mut parts := left.parts
    for (key, goal) in right.parts do
      if let some index := parts.findIdx? (·.1 == key) then
        parts := parts.set! index (key, mkAnd parts[index]!.2 goal)
      else parts := parts.push (key, goal)
    return ← withProofs parts fun proofs => do
      let inputs (own other : Partition) (projection : Name) : MetaM (Array Expr) :=
        own.parts.mapM fun (key, _) => do
          let some index := parts.findIdx? (·.1 == key) | throwError "missing partition key"
          if other.parts.any (·.1 == key) then mkAppM projection #[proofs[index]!]
          else pure proofs[index]!
      let proof ← mkAppM ``And.intro #[
        mkAppN left.reconstruct (← inputs left right ``And.left),
        mkAppN right.reconstruct (← inputs right left ``And.right)]
      return ⟨parts, ← mkLambdaFVars proofs proof⟩
  if expression.isAppOfArity ``ite 5 || expression.isAppOfArity ``dite 5 then
    let args := expression.getAppArgs
    if (← isProp expression) then
      let dependent := expression.isAppOf ``dite
      let branches ← if dependent then do
          let yes ← withLocalDeclD `condition args[1]! fun h => mkForallFVars #[h] (mkApp args[3]! h).headBeta
          let no ← withLocalDeclD `condition (mkNot args[1]!) fun h => mkForallFVars #[h] (mkApp args[4]! h).headBeta
          pure (mkAnd yes no)
        else do pure (mkAnd (← mkArrow args[1]! args[3]!) (← mkArrow (mkNot args[1]!) args[4]!))
      let child ← partition branches owner
      return ← withProofs child.parts fun proofs => do
        let valid := mkAppN child.reconstruct proofs
        let proof ← if dependent then mkAppM ``dite_of_branches #[args[1]!, args[3]!, args[4]!, valid]
          else mkAppM ``ite_of_branches #[args[1]!, args[3]!, args[4]!, valid]
        return ⟨child.parts, ← mkLambdaFVars proofs proof⟩
  if hasRequirement expression then
    throwError "unsupported logical form around a scoped requirement: {expression}"
  let parts := #[(owner, expression)]
  withProofs parts fun proofs => return ⟨parts, ← mkLambdaFVars proofs proofs[0]!⟩

/-- Publish stable names, including trivially discharged parts. The old combined
VC stays available as a lower-level interface but is no longer a proof field. -/
def scopedParts (name combined : Name) (headers : Array Nat) (total : Bool) :
    MetaM (Array Obligation × Name) := do
  let some expression := (← getConstInfo combined).value? | throwError "missing combined VC"
  let split ← partition expression
  let mut keys : Array PartKey := #[{}]
  for header in headers do
    for kind in #["init", "preservation"] ++ (if total then #["ranking"] else #[]) ++ #["exit"] do
      keys := keys.push { header, kind }
  for (key, _) in split.parts do
    unless keys.contains key do throwError "requirement names an unknown scoped loop: {key.field}"
  let mut obligations := #[]
  for key in keys do
    let raw := (split.parts.find? (·.1 == key)).map (·.2) |>.getD (mkConst ``True)
    let goal := name ++ `VC ++ key.field
    publishGoal goal raw #[] #[]
    obligations := obligations.push { field := key.field, goal, offset := key.header, kind := key.kind }
  let reconstructName := name ++ `execution_of_parts
  let domains := obligations.map fun o => ({ header := o.offset, kind := o.kind }, mkConst o.goal)
  withProofs domains fun proofs => do
    let inputs ← split.parts.mapM fun (key, _) => do
      let some index := keys.findIdx? (· == key) | throwError "missing published scoped part"
      mkAppM ``Eq.mpr #[mkConst (obligations[index]!.goal ++ `normalization), proofs[index]!]
    let proof := mkAppN split.reconstruct inputs
    addCheckedDeclaration (.thmDecl {
      name := reconstructName, levelParams := [],
      type := ← mkForallFVars proofs (mkConst combined), value := ← mkLambdaFVars proofs proof })
  discard <| audit reconstructName .checked
  return (obligations, reconstructName)

end VeriPyAsm.Verification.VC.Generation
