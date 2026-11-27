import QuasiRiemann
import Lean.Util.CollectAxioms

open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0

partial def auditExpr (e : Expr) (s : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .const n _ => s.insert n
  | .app f a => auditExpr a (auditExpr f s)
  | .lam _ t b _ => auditExpr b (auditExpr t s)
  | .forallE _ t b _ => auditExpr b (auditExpr t s)
  | .letE _ t v b _ => auditExpr b (auditExpr v (auditExpr t s))
  | .mdata _ b => auditExpr b s
  | .proj n _ b => auditExpr b (s.insert n)
  | _ => s

partial def auditClosure (env : Environment) (todo : List Name)
    (seen : Std.HashSet Name) : Std.HashSet Name :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then auditClosure env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => auditClosure env rest seen
      | some info =>
        let deps := auditExpr info.type {}
        let deps := match info with
          | .thmInfo i => auditExpr i.value deps
          | .defnInfo i => auditExpr i.value deps
          | .opaqueInfo i => auditExpr i.value deps
          | _ => deps
        auditClosure env (deps.toList ++ rest) seen

run_cmd do
  let env ← getEnv
  let target := ``OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
  let names := (auditClosure env [target] {}).toList.map toString
  let projectNames := names.filter (fun n => n.startsWith "OAI." ||
    n.startsWith "_private.OAI." || n.startsWith "RellichKondrachov." ||
    n.startsWith "PrimeNumberTheoremAnd.")
  liftIO <| IO.FS.writeFile "proof-dependency-cone.txt" (String.intercalate "\n" names)
  logInfo m!"declaration closure: {names.length}; recognized project names: {projectNames.length}"
