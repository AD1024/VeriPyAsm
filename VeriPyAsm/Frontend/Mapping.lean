import VeriPyAsm.Bytecode
import VeriPyAsm.Frontend.Elaboration

/-! Source positions propose annotation locations. This module checks their
control-flow interpretation against the admitted decoder output. The certificate
does not authenticate source locations or prove the CPython compiler correct.
VC generation independently checks cycle coverage and proves artifact semantics.
-/

namespace VeriPyAsm.Frontend

open CPython.V314 Lean

structure Span where
  line : Nat
  column : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, DecidableEq, BEq, ToJson

def Span.valid (s : Span) : Bool :=
  s.line > 0 && (s.line < s.endLine || (s.line == s.endLine && s.column < s.endColumn))

def Span.contains (outer inner : Span) : Bool :=
  inner.valid && (outer.line < inner.line ||
    (outer.line == inner.line && outer.column ≤ inner.column)) &&
    (inner.endLine < outer.endLine ||
      (inner.endLine == outer.endLine && inner.endColumn ≤ outer.endColumn))

structure LoopOrigin where
  label : String
  statement : Span
  test : Span
  body : Span
  deriving Repr, DecidableEq, BEq, ToJson

structure Source where
  schemaVersion : Nat := 1
  path : String
  digest : String
  functionName : String
  localNames : List String
  /-- One entry per two-byte code unit, including prefixes and caches. -/
  positions : List (Option Span)
  loop : LoopOrigin
  deriving Repr, DecidableEq, BEq, ToJson

structure Edge where
  sourcePC : Nat
  targetPC : Nat
  deriving Repr, DecidableEq, BEq, ToJson, ToExpr

structure Mapping where
  header : Nat
  testNodes : List Nat
  bodyNodes : List Nat
  entryEdges : List Edge
  backedges : List Edge
  bodyEdges : List Edge
  exitEdges : List Edge
  deriving Repr, DecidableEq, BEq, ToJson, ToExpr, Inhabited

structure ForestMapping where
  loops : List Mapping
  /-- Index of the immediate enclosing loop, or none for a root. -/
  parents : List (Option Nat)
  deriving Repr, DecidableEq, BEq, ToJson, ToExpr

private def successors (code : Code) (pc : Nat) : List Nat :=
  ((fetch code.instructions pc).map Instruction.successors).getD []

private def insert (xs : List Nat) (x : Nat) : List Nat :=
  if xs.contains x then xs else xs ++ [x]

private def closure (code : Code) (allowed : Nat → Bool) : Nat → List Nat → List Nat
  | 0, seen => seen
  | n + 1, seen =>
    let next := seen.foldl (fun found pc =>
      (successors code pc).foldl (fun acc target =>
        if allowed target then insert acc target else acc) found) seen
    if next == seen then seen else closure code allowed n next

/-- A finite graph with N vertices needs at most N reachability rounds. -/
def reachable (code : Code) (starts : List Nat) (allowed : Nat → Bool := fun _ => true) : List Nat :=
  closure code allowed code.instructions.length ((starts.filter allowed).foldl insert [])

def edges (code : Code) (nodes : List Nat) : List Edge :=
  nodes.flatMap fun pc => (successors code pc).map (fun target => ⟨pc, target⟩)

/-- Use the terminal opcode's position, never a cache/prefix as a boundary. -/
def position (artifact : Artifact) (source : Source) (pc : Nat) : Option Span := do
  let .ok (header, _) := Wordcode.read pc (artifact.code.drop pc) | none
  (source.positions[header.opcodeOffset / 2]?).join

private def within (artifact : Artifact) (source : Source) (span : Span) (pc : Nat) : Bool :=
  ((position artifact source pc).map span.contains).getD false

-- CPython can put a pure transport jump in the test span: when an inner loop
-- ends its enclosing body, its false arm jumps directly to the outer header.
private def testOp : Op → Bool
  | .loadConst _ | .loadSmallInt _ | .loadFast _ | .loadFastBorrow _ | .loadFastCheck _
  | .loadFastLoadFast _ _ | .loadFastBorrowLoadFastBorrow _ _ | .binary _ | .compare _
  | .toBool | .popJumpIfFalse _ _ | .popJumpIfTrue _ _ | .notTaken | .jump _ => true
  | _ => false

private def prune (code : Code) : Nat → List Nat → List Nat
  | 0, nodes => nodes
  | n + 1, nodes =>
    let remaining := nodes.filter (fun pc => (successors code pc).any nodes.contains)
    if remaining == nodes then nodes else prune code n remaining

/-- Independent finite check: removing the loop header leaves no reachable cycle. -/
def coveredMany (code : Code) (headers : List Nat) : Bool :=
  (prune code code.instructions.length ((reachable code [0]).filter (!headers.contains ·))).isEmpty

def covered (code : Code) (header : Nat) : Bool := coveredMany code [header]

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def checkMetadata (artifact : Artifact) (source : Source) : Except String Unit := do
  require (source.schemaVersion == 1) "unsupported source schema"
  require (!source.path.isEmpty && !source.digest.isEmpty) "missing source identity"
  require (source.functionName == artifact.name && source.localNames == artifact.localNames)
    "source function/local names disagree with the artifact"
  require (source.positions.length * 2 == artifact.code.length)
    "source position table must contain one entry per code unit"
  require (source.positions.all fun p => p.isNone || (p.getD ⟨0, 0, 0, 0⟩).valid)
    "invalid source span"

private def metadata (artifact : Artifact) (source : Source) : Except String Unit := do
  checkMetadata artifact source
  require (!source.loop.label.isEmpty && source.loop.statement.valid &&
    source.loop.statement.contains source.loop.test && source.loop.statement.contains source.loop.body &&
    !source.loop.body.contains source.loop.statement)
    "invalid loop source spans"

private def layout (artifact : Artifact) (source : Source) (code : Code) (header : Nat) : Mapping := Id.run do
  let all := reachable code [0]
  let allEdges := edges code all
  let testNodes := reachable code [header] (within artifact source source.loop.test)
  let outgoing := (edges code testNodes).filter (fun edge => !testNodes.contains edge.targetPC)
  let bodyEdges := outgoing.filter (fun edge => within artifact source source.loop.body edge.targetPC)
  let exitEdges := outgoing.filter (fun edge => !within artifact source source.loop.body edge.targetPC)
  let bodyNodes := reachable code (bodyEdges.map Edge.targetPC)
    (fun pc => pc != header && !(exitEdges.map Edge.targetPC).contains pc)
  return { header, testNodes, bodyNodes, bodyEdges, exitEdges
           entryEdges := allEdges.filter (fun e => e.targetPC == header && !bodyNodes.contains e.sourcePC)
           backedges := allEdges.filter (fun e => e.targetPC == header && bodyNodes.contains e.sourcePC) }

/-- Checks the proposed record, including complete edges, domination, empty-stack
header, test/body separation, and residual acyclicity. No disassembler graph is
accepted as evidence. Source association itself remains an external boundary. -/
def checkRegion (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights)
    (mapping : Mapping) : Except String Unit := do
  metadata artifact source
  let h := mapping.header
  let all := reachable code [0]
  require (all.contains h && (fetch code.instructions h).isSome)
    "header is not a reachable decoded instruction boundary"
  require (Stack.heightAt heights h == some 0) "loop header must have an empty operand stack"
  require (within artifact source source.loop.test h) "header does not start the source condition"
  require (mapping == layout artifact source code h) "mapping has incomplete or inconsistent regions/edges"
  require (!mapping.entryEdges.isEmpty && !mapping.backedges.isEmpty)
    "loop needs an entry and a backedge"
  require (!mapping.bodyEdges.isEmpty && !mapping.exitEdges.isEmpty)
    "condition must have both a body continuation and an exit"
  require (mapping.testNodes.all fun pc =>
    ((fetch code.instructions pc).map (fun i => testOp i.op)).getD false)
    "unsupported operation in source condition"
  let allEdges := edges code all
  require (allEdges.all fun e => !mapping.testNodes.contains e.targetPC || e.targetPC == h ||
    mapping.testNodes.contains e.sourcePC) "control flow enters the middle of the condition"
  require (mapping.bodyNodes.all fun pc => !mapping.testNodes.contains pc)
    "body overlaps the condition"
  let bypass := reachable code [0] (· != h)
  require (mapping.bodyNodes.all fun pc => !bypass.contains pc)
    "loop header does not dominate the body"
  require (mapping.backedges.all fun edge => !bypass.contains edge.sourcePC)
    "loop header does not dominate its backedges"

def check (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights)
    (mapping : Mapping) : Except String Unit := do
  checkRegion artifact source code heights mapping
  require (covered code mapping.header) "uncovered control-flow cycle; annotate every loop with veripy_sources"

/-- Candidate search is deliberately conservative: the current pinned while
pattern has a backward jump to the beginning of its condition. -/
def inferRegion (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights) :
    Except String Mapping := do
  metadata artifact source
  let all := reachable code [0]
  let candidates := code.instructions.foldl (fun found i =>
    match i.op with
    | .jump target =>
      if all.contains i.offset && target ≤ i.offset && within artifact source source.loop.test target
        then insert found target else found
    | _ => found) []
  let [header] := candidates
    | .error s!"cannot identify a unique while header (candidates {candidates}); missing positions or unsupported compiler pattern"
  let mapping := layout artifact source code header
  checkRegion artifact source code heights mapping
  return mapping

def infer (artifact : Artifact) (source : Source) (code : Code) (heights : Stack.Heights) :
    Except String Mapping := do
  let mapping ← inferRegion artifact source code heights
  check artifact source code heights mapping
  return mapping

private def parentOf (sources : List Source) (child : Source) : Option Nat :=
  let closest := sources.zipIdx.foldl (fun (best : Option (Source × Nat)) candidate =>
    if candidate.1.loop.body.contains child.loop.statement then
      match best with
      | none => some candidate
      | some previous => if previous.1.loop.body.contains candidate.1.loop.statement
          then some candidate else best
    else best) none
  closest.map Prod.snd

/-- Check the complete loop forest. Lexical nesting must agree with CFG nesting;
removing every certified header must leave an acyclic reachable graph. -/
def checkForest (artifact : Artifact) (sources : List Source) (code : Code)
    (heights : Stack.Heights) (forest : ForestMapping) : Except String Unit := do
  require (!sources.isEmpty && sources.length == forest.loops.length) "missing loop source/mapping"
  require (forest.parents == sources.map (parentOf sources)) "incorrect loop parent indices"
  for (source, mapping) in sources.zip forest.loops do
    checkRegion artifact source code heights mapping
  for (a, i) in (sources.zip forest.loops).zipIdx do
    for (b, j) in (sources.zip forest.loops).zipIdx do
      require (a.1.path == b.1.path && a.1.digest == b.1.digest && a.1.positions == b.1.positions)
        "loop sources disagree on source identity or positions"
      if i != j then
        require (a.1.loop.label != b.1.loop.label && a.2.header != b.2.header)
          "duplicate loop label or header"
        let nested := a.1.loop.body.contains b.1.loop.statement
        let reverse := b.1.loop.body.contains a.1.loop.statement
        let before := a.1.loop.statement.endLine < b.1.loop.statement.line ||
          (a.1.loop.statement.endLine == b.1.loop.statement.line &&
            a.1.loop.statement.endColumn ≤ b.1.loop.statement.column)
        let after := b.1.loop.statement.endLine < a.1.loop.statement.line ||
          (b.1.loop.statement.endLine == a.1.loop.statement.line &&
            b.1.loop.statement.endColumn ≤ a.1.loop.statement.column)
        require (nested || reverse || before || after) "overlapping loop source regions"
        require (nested == a.2.bodyNodes.contains b.2.header)
          "source nesting disagrees with control-flow nesting"
        if nested then
          require ((b.2.testNodes ++ b.2.bodyNodes).all a.2.bodyNodes.contains)
            "inner loop escapes its enclosing body"
  require (coveredMany code (forest.loops.map Mapping.header)) "uncovered control-flow cycle"

def inferForest (artifact : Artifact) (sources : List Source) (code : Code)
    (heights : Stack.Heights) : Except String ForestMapping := do
  let loops ← sources.mapM (fun source => inferRegion artifact source code heights)
  let forest := { loops, parents := sources.map (parentOf sources) }
  checkForest artifact sources code heights forest
  return forest

open Meta Elab Command Verification.VC Elaboration

private def readEdge (value : Expr) : MetaM Edge := do
  let value ← closed value
  let_expr Edge.mk source target := value | throwError "expected a mapping edge"
  return ⟨← readNat source, ← readNat target⟩

private def readMapping (value : Expr) : MetaM Mapping := do
  let value ← closed value
  let_expr Mapping.mk header test body entries backedges bodyEdges exits := value
    | throwError "expected a source mapping"
  return ⟨← readNat header, ← readList readNat test, ← readList readNat body,
    ← readList readEdge entries, ← readList readEdge backedges,
    ← readList readEdge bodyEdges, ← readList readEdge exits⟩

private def elaborateMapping (id admissionId sourceId : TSyntax `ident) (forest : Bool) : CommandElabM Unit := do
  let environment ← getEnv
  try
    let name := (← getCurrNamespace) ++ id.getId
    let admissionName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo admissionId
    let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo sourceId
    liftTermElabM do
      for input in #[admissionName, sourceName] do
        unless (← getConstInfo input).levelParams.isEmpty do
          throwError "source mapping requires closed inputs without universe parameters"
        discard <| audit input .checked
      let admission := mkConst admissionName
      let source := mkConst sourceName
      let admissionType ← whnf (← inferType admission)
      let_expr Admitted artifact := admissionType
        | throwError "source mapping requires an Admitted artifact"
      let sourceType := if forest then mkApp (mkConst ``List [.zero]) (mkConst ``Source) else mkConst ``Source
      unless (← isDefEq (← inferType source) sourceType) do
        throwError "source mapping requires Frontend.Source (or List Source for veripy_sources)"
      let structural ← mkAppM ``Admitted.toStackAdmitted #[admission]
      let translation ← mkAppM ``StackAdmitted.translation #[structural]
      let code ← mkAppM ``Embedding.Translation.code #[translation]
      let stack ← mkAppM ``StackAdmitted.stack #[structural]
      let heights ← mkAppM ``Stack.Certificate.heights #[stack]
      let result ← closed (← mkAppM (if forest then ``inferForest else ``infer) #[artifact, source, code, heights])
      if result.isAppOfArity ``Except.error 3 then
        let reason ← readString result.getAppArgs[2]!
        if forest then throwErrorAt sourceId "source loop forest rejected: {reason}"
        let path ← readString (← mkAppM ``Source.path #[source])
        let loop ← mkAppM ``Source.loop #[source]
        let span ← mkAppM ``LoopOrigin.statement #[loop]
        let line ← readNat (← mkAppM ``Span.line #[span])
        throwErrorAt sourceId "{path}:{line}: source mapping rejected: {reason}"
      unless result.isAppOfArity ``Except.ok 3 do throwError "source mapping did not reduce"
      -- Read constructor data with kernel reduction. Meta.reduce recursively
      -- unfolds graph computations before reducing them and grows prohibitively.
      let mapping ← if forest then do
          let value ← closed result.getAppArgs[2]!
          let_expr ForestMapping.mk loops parents := value | throwError "expected a loop forest"
          let parents ← readList (fun value => do
            let value ← closed value
            if value.isAppOfArity ``Option.none 1 then return none
            unless value.isAppOfArity ``Option.some 2 do throwError "expected a parent index"
            return some (← readNat value.getAppArgs[1]!)) parents
          pure (toExpr (ForestMapping.mk (← readList readMapping loops) parents))
        else pure (toExpr (← readMapping result.getAppArgs[2]!))
      publish name (mkConst (if forest then ``ForestMapping else ``Mapping)) mapping
      let check ← mkAppM (if forest then ``checkForest else ``check) #[artifact, source, code, heights, mkConst name]
      let result ← mkAppOptM ``Except.ok #[some (mkConst ``String), none, some (mkConst ``Unit.unit)]
      addCheckedDeclaration (.thmDecl {
        name := name ++ `valid, levelParams := [],
        type := ← mkEq check result, value := ← mkEqRefl check })
      discard <| audit (name ++ `valid) .checked
  catch error =>
    setEnv environment
    throw error

syntax (name := mapSource) "veripy_source " ident " from " ident " for " ident : command
syntax (name := mapSources) "veripy_sources " ident " from " ident " for " ident : command

@[command_elab mapSource] def elabMapSource : CommandElab := fun stx => do
  let `(veripy_source $id:ident from $admissionId:ident for $sourceId:ident) := stx
    | throwUnsupportedSyntax
  elaborateMapping id admissionId sourceId false

@[command_elab mapSources] def elabMapSources : CommandElab := fun stx => do
  let `(veripy_sources $id:ident from $admissionId:ident for $sourceId:ident) := stx
    | throwUnsupportedSyntax
  elaborateMapping id admissionId sourceId true

end VeriPyAsm.Frontend
