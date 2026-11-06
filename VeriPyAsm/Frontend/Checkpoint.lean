import VeriPyAsm.Frontend.Mapping

/-! Structural source checkpoints. Assertion regions include the failing raise;
logical boundaries retain complete edges, not just their shared destination PCs.
Acceptance proves neither the source claim nor its runtime correspondence. -/

namespace VeriPyAsm.Frontend
open CPython.V314 Lean

inductive CheckpointKind where
  | assertion | before | after
  deriving Repr, DecidableEq, BEq, ToJson, ToExpr

structure CheckpointOrigin where
  label : String
  kind : CheckpointKind
  /-- The whole assertion, or the statement immediately before/after the hint. -/
  statement : Span
  deriving Repr, DecidableEq, BEq, ToJson

structure CheckpointMapping where
  entry : Nat
  nodes : List Nat
  entryEdges : List Edge
  exitEdges : List Edge
  /-- Assertion entry edges; logical hints use entry or normal-exit edges. -/
  boundaryEdges : List Edge
  /-- Every explicit assertion failure in this region, including short circuiting. -/
  failureNodes : List Nat
  deriving Repr, DecidableEq, BEq, ToJson, ToExpr

namespace Checkpoint

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def nodes (artifact : Artifact) (source : Source) (code : Code)
    (origin : CheckpointOrigin) : List Nat :=
  (reachable code [0]).filter fun pc =>
    ((position artifact source pc).map origin.statement.contains).getD false

private def isFailure (code : Code) (pc : Nat) : Bool :=
  ((fetch code.instructions pc).map fun i => i.op == .raiseAssertionError).getD false

private def layout (code : Code) (origin : CheckpointOrigin) (region : List Nat)
    (entry : Nat) : CheckpointMapping :=
  let allEdges := edges code (reachable code [0])
  let entryEdges := allEdges.filter fun e => !region.contains e.sourcePC && region.contains e.targetPC
  let exitEdges := (edges code region).filter fun e => !region.contains e.targetPC
  { entry, nodes := region, entryEdges, exitEdges
    boundaryEdges := if origin.kind == .after then exitEdges else entryEdges
    failureNodes := region.filter (isFailure code) }

private def assertionOp : Op → Bool
  | .loadConst _ | .loadSmallInt _ | .loadFast _ | .loadFastBorrow _ | .loadFastCheck _
  | .loadFastLoadFast _ _ | .loadFastBorrowLoadFastBorrow _ _ | .binary _ | .compare _
  | .toBool | .popJumpIfFalse _ _ | .popJumpIfTrue _ _ | .notTaken | .jump _
  | .loadAssertionError | .raiseAssertionError => true
  | _ => false

-- A fused store can hide a source statement boundary even if its single
-- retained position belongs to just one of the original instructions.
private def fusedStore (code : Code) (pc : Nat) : Bool :=
  ((fetch code.instructions pc).map fun i => match i.op with
    | .storeFastLoadFast _ _ | .storeFastStoreFast _ _ => true
    | _ => false).getD false

/-- Independently recomputes complete regions and edges from decoded groups.
The conservative single-entry check rejects duplicated/eliminated boundaries.
Hint edges may have shared targets; consumers must preserve their edge scope. -/
def check (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights)
    (origin : CheckpointOrigin) (mapping : CheckpointMapping) : Except String Unit := do
  checkMetadata artifact source
  require (!origin.label.isEmpty && origin.statement.valid) "invalid checkpoint origin"
  let all := reachable code [0]
  require (all.all fun pc =>
    ((fetch code.instructions pc).map fun i => i.op == .resume).getD false ||
      (position artifact source pc).isSome) "checkpoint mapping requires complete instruction positions"
  let region := nodes artifact source code origin
  require (!region.isEmpty) "checkpoint statement has no reachable decoded region (removed or missing positions)"
  require (mapping == layout code origin region mapping.entry)
    "checkpoint mapping has incomplete or inconsistent regions/edges"
  require (region.contains mapping.entry && (fetch code.instructions mapping.entry).isSome)
    "checkpoint entry is not a decoded instruction boundary"
  require (!mapping.entryEdges.isEmpty && mapping.entryEdges.all (·.targetPC == mapping.entry))
    "checkpoint statement must have one entry; duplicated or interior entry is unsupported"
  require (Stack.heightAt heights mapping.entry == some 0)
    "checkpoint statement entry must have an empty operand stack"
  let connected := reachable code [mapping.entry] region.contains
  require (region.all connected.contains) "checkpoint statement has disconnected source regions"
  let bypass := reachable code [0] (· != mapping.entry)
  require (region.all fun pc => !bypass.contains pc) "checkpoint entry does not dominate its region"
  require (!(region ++ mapping.entryEdges.map Edge.sourcePC).any (fusedStore code))
    "fused stores may erase the requested source boundary"
  require (!mapping.boundaryEdges.isEmpty) "checkpoint has no normal boundary (removed or terminal statement)"
  require (mapping.boundaryEdges.all fun e =>
    (fetch code.instructions e.sourcePC).isSome && (fetch code.instructions e.targetPC).isSome &&
      Stack.heightAt heights e.targetPC == some 0)
    "checkpoint edges must end at decoded boundaries with empty operand stacks"
  if origin.kind == .assertion then
    require (region.all fun pc =>
      ((fetch code.instructions pc).map fun i => assertionOp i.op).getD false)
      "unsupported operation in assertion region"
    require (mapping.failureNodes.length == 1) "assertion needs one explicit failure site"
    require (region.all fun pc =>
      !(reachable code ((edges code [pc]).map Edge.targetPC) region.contains).contains pc)
      "assertion evaluation region contains a cycle"
    require (mapping.exitEdges.all fun e => Stack.heightAt heights e.targetPC == some 0)
      "assertion passing exits must have an empty operand stack"

def infer (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights)
    (origin : CheckpointOrigin) : Except String CheckpointMapping := do
  let region := nodes artifact source code origin
  let entries := ((edges code (reachable code [0])).filter fun e =>
    !region.contains e.sourcePC && region.contains e.targetPC).map Edge.targetPC
  let entry := entries.headD 0
  let mapping := layout code origin region entry
  check artifact source code heights origin mapping
  return mapping

def checkAll (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights)
    (origins : List CheckpointOrigin) (mappings : List CheckpointMapping) : Except String Unit := do
  require (origins.length == mappings.length) "missing checkpoint mapping"
  require ((origins.map (·.label)).eraseDups.length == origins.length) "duplicate checkpoint label"
  for (origin, mapping) in origins.zip mappings do
    check artifact source code heights origin mapping

def inferAll (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights)
    (origins : List CheckpointOrigin) : Except String (List CheckpointMapping) := do
  let mappings ← origins.mapM fun origin => do
    match infer artifact source code heights origin with
    | .ok mapping => return mapping
    | .error reason => .error s!"{source.path}:{origin.statement.line}: {origin.label}: {reason}"
  checkAll artifact source code heights origins mappings
  return mappings

end Checkpoint

open Meta Elab Command Verification.VC Elaboration

private def readCheckpoint (value : Expr) : MetaM CheckpointMapping := do
  let value ← closed value
  let_expr CheckpointMapping.mk entry nodes entries exits boundaries failures := value
    | throwError "expected a checkpoint mapping"
  let readEdge := fun value => do
    let value ← closed value
    let_expr Edge.mk source target := value | throwError "expected a checkpoint edge"
    return Edge.mk (← readNat source) (← readNat target)
  return ⟨← readNat entry, ← readList readNat nodes, ← readList readEdge entries,
    ← readList readEdge exits, ← readList readEdge boundaries, ← readList readNat failures⟩

syntax (name := mapCheckpoints) "veripy_checkpoints " ident " from " ident
  " for " ident " at " ident : command

@[command_elab mapCheckpoints] def elabMapCheckpoints : CommandElab := fun stx => do
  let `(veripy_checkpoints $id:ident from $admissionId:ident for $sourceId:ident at $originsId:ident) := stx
    | throwUnsupportedSyntax
  let environment ← getEnv
  try
    let name := (← getCurrNamespace) ++ id.getId
    let admissionName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo admissionId
    let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo sourceId
    let originsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo originsId
    liftTermElabM do
      for input in #[admissionName, sourceName, originsName] do
        unless (← getConstInfo input).levelParams.isEmpty do
          throwError "checkpoint mapping requires closed inputs without universe parameters"
        discard <| audit input .checked
      let admission := mkConst admissionName
      let source := mkConst sourceName
      let origins := mkConst originsName
      let admissionType ← whnf (← inferType admission)
      let_expr Admitted artifact := admissionType
        | throwError "checkpoint mapping requires an Admitted artifact"
      unless (← isDefEq (← inferType source) (mkConst ``Source)) do
        throwError "checkpoint mapping requires Frontend.Source"
      let listType := fun name => mkApp (mkConst ``List [.zero]) (mkConst name)
      unless (← isDefEq (← inferType origins) (listType ``CheckpointOrigin)) do
        throwError "checkpoint mapping requires List Frontend.CheckpointOrigin"
      let structural ← mkAppM ``Admitted.toStackAdmitted #[admission]
      let translation ← mkAppM ``StackAdmitted.translation #[structural]
      let code ← mkAppM ``Embedding.Translation.code #[translation]
      let stack ← mkAppM ``StackAdmitted.stack #[structural]
      let heights ← mkAppM ``Stack.Certificate.heights #[stack]
      let inputs := #[artifact, source, code, heights, origins]
      let result ← closed (← mkAppM ``Checkpoint.inferAll inputs)
      if result.isAppOfArity ``Except.error 3 then
        throwErrorAt originsId "source checkpoints rejected: {← readString result.getAppArgs[2]!}"
      unless result.isAppOfArity ``Except.ok 3 do throwError "checkpoint mapping did not reduce"
      let mappings ← readList readCheckpoint result.getAppArgs[2]!
      publish name (listType ``CheckpointMapping) (toExpr mappings)
      let check ← mkAppM ``Checkpoint.checkAll (inputs.push (mkConst name))
      let ok ← mkAppOptM ``Except.ok #[some (mkConst ``String), none, some (mkConst ``Unit.unit)]
      addCheckedDeclaration (.thmDecl {
        name := name ++ `valid, levelParams := [], type := ← mkEq check ok, value := ← mkEqRefl check })
      discard <| audit (name ++ `valid) .checked
  catch error =>
    setEnv environment
    throw error

end VeriPyAsm.Frontend
