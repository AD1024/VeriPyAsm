import VeriPyAsm.Verification.VC.Generation

/-! Checkpoint-specific declaration planning. The graph validates labels/edges
for diagnostics; `CheckpointSpecification.verified` carries the soundness proof. -/

namespace VeriPyAsm.Verification.VC.Generation
open Lean Meta Semantics

private def readString (value : Expr) : MetaM String := do
  if let some text := getStringValue? (← closedWhnf value) then return text
  let chars ← readList (← mkAppM ``String.toList #[value])
  return String.ofList (← chars.toList.mapM fun char => do
    return Char.ofNat (← readNat (← mkAppM ``Char.toNat #[char])))

def checkpointGoals (name : Name) (next spec : Expr) (fuel : Nat)
    (graph : Array (Nat × Array Nat)) : MetaM (Array Expr × Array Obligation) := do
  let checks ← mkAppM ``CheckpointSpecification.checkpoints #[spec]
  let values ← readList checks
  let indices ← readList (← mkAppM ``List.finRange #[mkNatLit values.size])
  let mut labels : Array String := #[]
  let mut goals := #[]
  let mut obligations := #[]
  for value in values, index in indices do
    let label ← readString (← mkAppM ``EdgeCheckpoint.label #[value])
    if label.isEmpty || labels.contains label then throwError "empty or duplicate checkpoint label: {label}"
    labels := labels.push label
    let kind ← readString (← mkAppM ``EdgeCheckpoint.kind #[value])
    let edges ← (← readList (← mkAppM ``EdgeCheckpoint.edges #[value])).mapM fun edge => do
      let source ← readNat (← mkAppM ``Prod.fst #[edge])
      let target ← readNat (← mkAppM ``Prod.snd #[edge])
      return (source, target)
    if edges.isEmpty then throwError "checkpoint {label} has no edges"
    for (source, target) in edges do
      unless graph.any (fun (pc, successors) => pc == source && successors.contains target) do
        throwError "checkpoint {label} uses a nonexistent decoded edge {source} -> {target}"
    let field := Name.mkSimple s!"checkpoint_{label}"
    goals := goals.push (← mkAppM ``CheckpointSpecification.SelectedVC #[next, spec, mkNatLit fuel, index])
    obligations := obligations.push { field, goal := name ++ `VC ++ field, offset := edges[0]!.2, kind }
  return (goals, obligations)

end VeriPyAsm.Verification.VC.Generation
