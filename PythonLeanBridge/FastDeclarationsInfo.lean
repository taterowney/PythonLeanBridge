import PythonLeanBridge.Frontend
import Lean
import Lean.CoreM
import PythonLeanBridge.States

open Lean System IO Core Meta

/-- Premises from a module whose name has one of the following as a component are not retrieved. -/
def moduleBlackListExtended : Array String := #[
  "Aesop", "Auto", "Cli", "CodeAction", "DocGen4", "Duper", "ImportGraph", "Lake", "Lean", "LeanSearchClient", "Linter", "Mathport",
  "MD4Lean", "Plausible", "ProofWidgets", "Qq", "QuerySMT", "Tactic", "TacticExtra", "Test", "Testing", "UnicodeBasic", "Util",
  "Init.Grind", "Init.Control", "Init.Meta", "Init.Syntax", "Init.System", "Std.Sat", "Std.Tactic"
]

def findLean (mod : Name) : IO FilePath := do
  let srcSearchPath : Lean.SearchPath ← initSrcSearchPath
  if let some fname ← srcSearchPath.findModuleWithExt "lean" mod then
    return fname
  else
    let mut fname := FilePath.mk ((← findOLean mod).toString.replace ".lake/build/lib/" "") |>.withExtension "lean"
    if !(← fname.pathExists) then
      -- Might be in an exe, on Mac, and the module is from Init, Lean, etc.
      fname := FilePath.mk ((← findOLean mod).toString.replace "lib/" "src/") |>.withExtension "lean"
      if !(← fname.pathExists) then
        -- If not found, throw an error
        throw <| IO.userError s!"Path to {mod} not found"
    return fname


def ppExprIO (ctx : PPContext) (expr : Expr) : IO String :=
  ctx.runMetaM do
    let expr ← instantiateMVars expr
    let fmt ← PrettyPrinter.ppExpr expr
    pure fmt.pretty

def ppExprIOReduceType (ctx : PPContext) (expr : Expr) : IO String :=
  ctx.runMetaM do
    let expr ← instantiateMVars expr
    let expr ← whnf expr
    let expr ← zetaReduce expr
    let expr ← betaReduce expr

    let fmt ← PrettyPrinter.ppExpr expr
    pure fmt.pretty

def streamAllConstantInfos (modules : Array Name) : IO Unit := do
  initSearchPath (← getLibDir (← findSysroot))
  unsafe Lean.enableInitializersExecution
  let env ← importModules (modules.map (Import.mk · false)) Options.empty (leakEnv := true)

  CoreM.withImportModules modules (do
    let context := PPContext.mk env {} .empty {} .anonymous []


    let mut modsMap : Std.HashMap Name (List (Name × ConstantInfo × DeclarationRanges)) := Std.HashMap.empty
    -- Loop through all constants, find which ones are explicitly in modules
    for ⟨name, ci⟩ in env.constants do
      let mod ← Lean.findModuleOf? name
      match mod with
      | none => continue
      | some module =>
        -- Keep only theorems/definitions with real modules...
        -- if (ci.isTheorem || ci.isDefinition) && (module != Name.anonymous) && (modules.contains module) then
        if (ci.isTheorem || ci.isDefinition) && (module != Name.anonymous) then
          unless moduleBlackList.any (fun p => module.anyS (· == p)) && !(module.toString.startsWith "LeanRAG") do
          -- ...and only those that have corresponding source code (other ones are spawned goals, etc.)
            match (← findDeclarationRanges? name) with
            | none => continue
            | some rgs =>
              if let some l := modsMap.get? module then
                modsMap := modsMap.insert module (l ++ [(name, ci, rgs)])
              else
                modsMap := modsMap.insert module [(name, ci, rgs)]

    for module in modsMap.keys do
      let modulePath ← findLean module
      let fileContents ← IO.FS.readFile modulePath.toString
      for ⟨name, ci, rgs⟩ in modsMap.getD module [] do
        let kind := if ci.isTheorem then "theorem" else "definition"
        let declTextList := if rgs.range.pos.line == 0 then [] else
          fileContents.splitOn "\n"
            |>.drop (rgs.range.pos.line - 1)
            |>.take (rgs.range.endPos.line - rgs.range.pos.line + 1)
        let declText := "\n".intercalate declTextList

        let deps := ci.getUsedConstantsAsSet.toList
        let mut deps_with_mods : List Json := []
        for dep in deps do
          if let some dep_mod := (← Lean.findModuleOf? dep) then
            deps_with_mods := (Json.mkObj [("name", Json.str dep.toString), ("module", Json.str dep_mod.toString)]) :: deps_with_mods

        let type ← ppExprIOReduceType context ci.type -- TODO: make sure this isn't a time sink; widen monad?
        let initialProofState ← getInitialProofState env ci -- basically the same as `type`; are these redundant?

        let j := Json.mkObj [
          ("name", Json.str name.toString),
          ("module", Json.str module.toString),
          ("kind", Json.str kind),
          ("text", Json.str declText),
          ("dependencies", Json.arr deps_with_mods.toArray),
          -- ("value", Json.str value),
          ("type", Json.str type),
          ("initialProofState", Json.str initialProofState)
        ]
        -- printAndFlush <| (toJson j).compress ++ "\n"
        IO.println (toJson j).compress
  )

unsafe def get_decls (modulesString : String) : IO Nat := do
  let modules := modulesString.splitOn "," |>.map (fun m => m.toName) |>.toArray
  streamAllConstantInfos modules
  return 0

def testfn (arg : Nat) : IO Nat := do
  if arg == 1 then
    IO.println "triggered"
    -- throw <| IO.userError "Function called with true" -- Simulate an error
    return 1
  else
    return 0

def main (_args : List String) : IO UInt32 := do
  -- let _ := IO.setStdout (IO.FS.Stream.ofBuffer <|
  --   ← ST.mkRef <|
  --   FS.Stream.Buffer.mk ByteArray.empty 1)

  streamAllConstantInfos #[`LeanRAG.Basic]
  return 0

-- #min_imports
