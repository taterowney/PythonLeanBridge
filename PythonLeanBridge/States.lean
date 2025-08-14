import PythonLeanBridge.Frontend
import PythonLeanBridge.Deps
import Lean
import Cli

-- open Lean Meta Core Cli
open Lean Core Elab IO Meta Term Command Tactic Cli MetaM Frontend

set_option autoImplicit true

/- Set this to false if you also want to extract proof states for definitions -/
-- def theoremsOnly := true

/- Extracts the initial proof state of a constant. -/
-- def getInitialProofState (env : Environment) (ci : ConstantInfo) : IO String := do
--   let (state, _, _) ← MetaM.toIO (ctxCore := { fileName := "", fileMap := default }) (sCore := { env }) do
--     -- forallTelescope transforms ∀ n : Nat, 0 + n = n to _args = #[n : Nat] and typ = 0 + n = n
--     forallTelescope ci.type fun _args typ => do
--       let g ← mkFreshExprMVar typ
--       g.mvarId!.withContext do
--         -- We disable some pretty-printing options,
--         -- e.g. Nat is not pretty-printed as ℕ
--         -- HAdd.hAdd is not pretty-printed as +
--         let state ← withOptions (fun o => o.set `pp.notation false |>.set `pp.fullNames true) <| Meta.ppGoal g.mvarId!
--         return state.pretty (width := 100000000)
--   return state

/-- Premises from a module whose name has one of the following as a component are not retrieved. -/
def moduleBlackList : Array String := #[
  "Aesop", "Auto", "Cli", "CodeAction", "DocGen4", "Duper", "ImportGraph", "Lake", "Lean", "LeanSearchClient", "Linter", "Mathport",
  "MD4Lean", "Plausible", "ProofWidgets", "Qq", "QuerySMT", "Tactic", "TacticExtra", "Test", "Testing", "UnicodeBasic", "Util"
]

/-- A premise whose name has one of the following as a component is not retrieved. -/
def nameBlackList : Array String := #["Lean", "Lake", "Qq"]

/-- A premise whose `type.getForallBody.getAppFn` is a constant that has this prefix is not retrieved. -/
def typePrefixBlackList : Array Name := #[`Lean]

def isBlackListedPremise (env : Environment) (name : Name) (theoremsOnly : Bool := true) : Bool := Id.run do
  if name == ``sorryAx then return true
  if name.isInternalDetail then return true
  if nameBlackList.any (fun p => name.anyS (· == p)) then return true
  -- let some moduleName := env.getModuleFor? name | return true
  -- if moduleBlackList.any (fun p => moduleName.anyS (· == p)) then return true
  let some ci := env.find? name | return true
  match ci with
  | .thmInfo _ => pure ()
  | .defnInfo _ => if theoremsOnly then return true
  | _ => return true
  if let .const fnName _ := ci.type.getForallBody.getAppFn then
    if typePrefixBlackList.any (fun p => p.isPrefixOf fnName) then return true
  return false

structure Dependency where
  name : Name
  module : Name
  kind : String
deriving Repr, ToJson

structure Result where
  name : Name
  kind : String
  module : Name
  initial_proof_state : String
  src : String
  dependencies : List Dependency := []
deriving Repr, ToJson


def getInitialProofState (env : Environment) (ci : ConstantInfo) : IO String := do
  try
    let (state, _, _) ← MetaM.toIO (ctxCore := { fileName := "", fileMap := default }) (sCore := { env }) do
      -- forallTelescope transforms ∀ n : Nat, 0 + n = n to _args = #[n : Nat] and typ = 0 + n = n
      forallTelescope ci.type fun _args typ => do
        let typ ← zetaReduce typ
        let typ ← betaReduce typ
        let typ ← whnf typ
        let g ← mkFreshExprMVar typ
        g.mvarId!.withContext do
          -- We disable some pretty-printing options,
          -- e.g. Nat is not pretty-printed as ℕ
          -- HAdd.hAdd is not pretty-printed as +
          let state ← withOptions (fun o => o.set `pp.notation false |>.set `pp.fullNames true) <| Meta.ppGoal g.mvarId!
          return state.pretty (width := 100000000)
    return state
  catch _ =>
    return default
    -- let backup:=  match InfoTree. cmd.trees |>.get? 0 with
    -- | some t => t.mainGoalStateBefore
    -- | _ => pure default
    -- return (← backup).pretty (width := 100000000)


open Elab.IO in
def allProofStatesFromModule (targetModule : Name) (decls : Option (List Name)) (proofAsSorry? : Bool) (theoremsOnly : Bool := true) : IO (Array Result) := do
  -- Don't extract anything from blacklisted modules
  if moduleBlackList.any (fun p => targetModule.anyS (· == p)) then
    return #[]

  searchPathRef.set compile_time_search_path%
  let fileName := (← findLean targetModule).toString

  /- Replace all tactics with "sorry" for faster execution -/
  let proofAsSorry := ({} : KVMap).insert `debug.byAsSorry (.ofBool true)
    |>.insert `linter.unusedVariables (.ofBool false)
    |>.insert `linter.unusedTactic (.ofBool false)
    |>.insert `linter.unreachableTactic (.ofBool false)

  let options := if proofAsSorry? then proofAsSorry else {}
  let steps := processInput' (← moduleSource targetModule) none options fileName
  let targets := steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)

  let mut results : Array Result := #[]

  for (cmd, ci) in targets do
    let ci_name_stem := ci.name.toString.splitOn "." |>.getLast! |>.toName
    if (decls.isSome && !((decls.get!.contains ci_name_stem) || decls.get!.contains ci.name)) then
      continue

    let env := cmd.after
    let name := ci.name
    let isThm := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless isBlackListedPremise env name theoremsOnly do
      let deps ← getContext cmd
      let result : Result := {
        name := name,
        kind := isThm,
        module := targetModule,
        initial_proof_state := ← getInitialProofState env ci,
        src := toString cmd.src
        dependencies := deps.map fun d =>
          { name := d.name, module := d.module, kind := d.kind }
      }
      results := results.push result

  return results
