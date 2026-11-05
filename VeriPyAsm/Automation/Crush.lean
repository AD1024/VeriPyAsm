import VeriPyAsm.Verification.VC.Discharge
import Crush

/-! Optional adapter for the pinned Crush revision. We force the selected trust
policy and disable native/bitvector trust. Actual route information comes from
Crush's result trace, not from the configured reconstruction mode. Missing trace
events remain unknown. The core independently kernel-checks and audits evidence.
-/

namespace VeriPyAsm.Automation.Crush

open Lean Meta Elab VeriPyAsm.Verification.VC

/-- Preserve the original diagnostic as well as this best-effort classification.
These phrases are from the pinned Crush driver/process implementation. -/
def failureKind (message : String) : String :=
  -- Every unknown diagnostic suggests changing `crush.timeout`; that suggestion
  -- alone is not evidence that a timeout actually occurred.
  if message.contains "returned `unknown`" then
    if message.contains "(timeout)" || message.contains "timed out" then "timeout" else "unknown"
  else if message.contains "timed out" then "timeout"
  else if message.contains "reconstruction" || message.contains "Alethe" then "reconstruction_failed"
  else if message.contains "solver found a" then "sat"
  else if message.contains "unsupported" || message.contains "translation" ||
      message.contains "SMT sort error" then "unsupported_translation"
  else if message.contains "could not execute" || message.contains "no such file" ||
      message.contains "executable" || message.contains "process" then "backend_error"
  else "automation_failed"

private def observedPath (events : Array String) : Option String :=
  if events.any (·.contains "proof replay succeeded") then some "alethe_replay"
  else if events.any (·.contains "reconstruction succeeded; no axiom used") then some "core_reconstruction"
  else if events.any (·.contains "pre-translation checked proof succeeded") then some "checked_before_smt"
  else if events.any (·.contains "goal is one of the selected facts") then some "selected_fact"
  else none

def solve (config : VeriPyAsm.Verification.VC.Config) (type : Expr) : TermElabM Attempt :=
  withOptions (fun options => options
    |>.set `crush.backend config.backend
    |>.set `crush.timeout config.timeout
    |>.set `crush.trust (if config.policy == .checked then "reconstruct" else "trust")
    |>.setBool `crush.reconstruct.trustBvDecide false
    |>.setBool `crush.reconstruct.trustNativeDecide false
    |>.setBool `crush.profile false
    |>.setBool `trace.crush false
    |>.setBool `trace.crush.result true) do
    let previousTraces ← getTraceState
    setTraceState {}
    try
      -- Crush's binder introduction does not unfold arbitrary named VC defs.
      -- Expose their bodies by definitional reduction; the core checks the
      -- resulting proof against the original named proposition afterwards.
      let expanded ← withTransparency .all <| whnf type
      let goal ← mkFreshExprMVar expanded .syntheticOpaque
      let mut attempt : Attempt := {}
      try
        let remaining ← Tactic.run goal.mvarId! <| Tactic.withoutRecover do
          Tactic.evalTactic (← `(tactic| crush))
        unless remaining.isEmpty do throwError "Crush left unsolved goals"
        let proof ← instantiateMVars goal
        attempt := { attempt with proof := some proof }
      catch error =>
        let detail ← error.toMessageData.toString
        attempt := { attempt with failureKind := failureKind detail, detail }
      let events ← (← getTraces).toArray.mapM (fun event => event.msg.toString)
      let sawSolver := events.any (·.contains "unsat; core facts") ||
        ["sat", "unknown", "timeout"].contains attempt.failureKind
      let path := observedPath events
      let path := if path.isNone && attempt.proof.any
          (·.getUsedConstants.contains `Crush.crushSorryWith) then some "solver_trust" else path
      return { attempt with
        events, path,
        actualBackend := if sawSolver then some config.backend else none }
    finally
      setTraceState previousTraces

initialize installSolver solve

end VeriPyAsm.Automation.Crush
