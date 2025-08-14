import Lean
import Lean.CoreM
import Cli

open Lean System IO Cli Elab



open Core in
def CoreM.withImportModules {α : Type} (modules : Array Name) (run : CoreM α)
    (searchPath : Option Lean.SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp else
    initSearchPath (← getLibDir (← findSysroot))
  Lean.withImportModules (modules.map (fun m => Import.mk m false)) options (trustLevel := trustLevel) fun env =>
    let ctx := {fileName, options, fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      run

structure CommandResult where
  value : String := ""
  type : String := ""
  error : String := ""
deriving Repr, ToJson

def Expr.isForall : Expr → Bool
  | .forallE .. => true
  | _           => false

def Expr.forallDomain (e : Expr) (h : isForall e = true) : Expr :=
  match e, h with
  | .forallE _ d _ _, _ => d



unsafe def functionFromString (fn_name : String) (arg : String) : CoreM (CommandResult) := do
  try
    let mut type := (← getConstInfo (Name.mkStr1 fn_name)).type

    if h : type.isForall then
      let mut argType := Expr.forallDomain type h
      let mut retType := type.getForallBody

      if (type.dbgToString.splitOn ("->") |>.length) != 2 then
        return {
          type := "Error",
          error := s!"Error: Expected function with 1 argument, but got {(type.dbgToString.splitOn ("->") |>.length) - 1}."
        }

      let input_fn := match argType.dbgToString with
      | "String" =>
        fun (β : Type) (post : β → CoreM CommandResult) => do
          let fn ← evalConst (String → β) (Name.mkStr1 fn_name)
          post (fn arg)

      | "Bool" =>
        match arg with
        | "true" =>
          fun (β : Type) (post : β → CoreM CommandResult) => do
            let fn ← evalConst (Bool → β) (Name.mkStr1 fn_name)
            post (fn true)
        | "True" =>
          fun (β : Type) (post : β → CoreM CommandResult) => do
            let fn ← evalConst (Bool → β) (Name.mkStr1 fn_name)
            post (fn true)
        | "false" =>
          fun (β : Type) (post : β → CoreM CommandResult) => do
            let fn ← evalConst (Bool → β) (Name.mkStr1 fn_name)
            post (fn false)
        | "False" =>
          fun (β : Type) (post : β → CoreM CommandResult) => do
            let fn ← evalConst (Bool → β) (Name.mkStr1 fn_name)
            post (fn false)
        | _ =>
          fun _ _ => pure (CommandResult.mk (type := "Error") (error := s!"Error: Couldn't interpret {arg} as Bool.") (value := ""))

      | "Nat" =>
        match arg.toNat? with
        | some n =>
          fun (β : Type) (post : β → CoreM CommandResult) => do
            let fn ← evalConst (Nat → β) (Name.mkStr1 fn_name)
            post (fn n)
        | none =>
          fun _ _ => pure (CommandResult.mk (type := "Error") (error := s!"Error: Couldn't interpret {arg} as Nat.") (value := ""))

      | "Lean.Json" =>
        match Json.parse arg |>.toOption with
        | some json =>
          fun (β : Type) (post : β → CoreM CommandResult) => do
            let fn ← evalConst (Json → β) (Name.mkStr1 fn_name)
            post (fn json)
        | none =>
          fun _ _ => pure (CommandResult.mk (type := "Error") (error := s!"Error: Couldn't parse {arg} as Json.") (value := ""))

      | "Unit" =>
        fun (β : Type) (post : β → CoreM CommandResult) => do
          let fn ← evalConst (Unit → β) (Name.mkStr1 fn_name)
          post (fn ())

      | _ => fun _ _ => pure (CommandResult.mk (type := "Error") (error := s!"Error: Expected return type String, Nat, Json, Unit, or IO Unit, but got {retType.dbgToString}.") (value := ""))

      try
        let res : CoreM CommandResult ← match retType.dbgToString with
        | "String" =>
          input_fn String (fun s => do return CommandResult.mk (value := s) (type := "String") (error := ""))
        | "IO String" =>
          input_fn (IO String) (fun s => do return CommandResult.mk (← s) (type := "String") (error := ""))

        | "Bool" =>
          input_fn Bool (fun s => do return CommandResult.mk (value := toString s) (type := "Bool") (error := ""))
        | "IO Bool" =>
          input_fn (IO Bool) (fun s => do return CommandResult.mk (value := toString (← s)) (type := "Bool") (error := ""))

        | "Nat" =>
          input_fn Nat (fun s => do return CommandResult.mk (value := toString s) (type := "Nat") (error := ""))
        | "IO Nat" =>
          input_fn (IO Nat) (fun s => do return CommandResult.mk (value := toString (← s)) (type := "Nat") (error := ""))

        | "Lean.Json" =>
          input_fn Json (fun s => do return CommandResult.mk (value := s.compress) (type := "Json") (error := ""))
        | "IO Lean.Json" =>
          input_fn (IO Json) (fun s => do return CommandResult.mk (value := (← s).compress) (type := "Json") (error := ""))

        -- | "Unit" =>
        --   input_fn Unit (fun s => do return CommandResult.mk (value := "") (type := "None") (error := ""))
        | "IO Unit" =>
          input_fn (IO Unit) (fun s => do
            let _ ← s
            return CommandResult.mk (value := "") (type := "None") (error := ""))

        | _ => pure <| CommandResult.mk (type := "Error") (error := s!"Error: Expected return type String, Nat, Json, Unit, or IO Unit, but got {retType.dbgToString}.") (value := "")
        return res
      catch e =>
        return {
          type := "Error",
          error := s!"Error while running function: {← e.toMessageData.toString}",
          value := ""
        }

    else
      return {
        type := "Error",
        error := s!"Not a function"
      }

  catch _ =>
    return {
      type := "Error",
      error := s!"Error: Function {fn_name} not found."
    }


def printAndFlush (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr s
  out.flush


unsafe def repl (args : Cli.Parsed) : IO UInt32 := do
  let modules := args.positionalArg! "module" |>.as? String |>.getD ""
    |>.splitOn ","
    |>.map (fun m => m.toName)
    |>.toArray

  -- let printResult := args.positionalArg? "printOutput" |>.getD default |>.as? Bool |>.getD true
  -- let printResult := true
  try
    CoreM.withImportModules modules (do
      loop
    )
  catch e =>
    printAndFlush ("{\"value\": \"\", \"type\": \"Error\", \"error\": \"" ++ e.toString ++ "\"}\n")
    return (1 : UInt32)


  where loop : CoreM UInt32 := do
    let query ← (← IO.getStdin).getLine
    if query = "\n" then
      loop else
    match (Json.parse <| query).toOption with
    | some json => do
      let fn_name := json.getObjVal? "name" |>.toOption.getD "" |>.getStr?.toOption.getD ""
      let arg := match json.getObjVal? "arg" |>.toOption.getD "" |>.getStr?.toOption with
        | some s => s
        | none => json.getObjVal? "arg" |>.toOption.getD "" |>.compress
      let printResult? := match json.getObjVal? "printResult" |>.toOption.getD (Json.bool true) with
        | Json.bool b => b
        | _ => true

      let res := (toJson (← functionFromString fn_name arg) |>.compress)
      if printResult? then printAndFlush <| res ++ "\n"

    | none => printAndFlush "{\"error\": \"Invalid JSON input\", \"value\": \"\", \"type\": \"Error\"}\n"

    printAndFlush "2131792754394826543\n" -- Unlikely to be printed by a random IO.println
    loop


unsafe def bridge : Cmd := `[Cli|
  -- bridge VIA runFunctionMain; ["0.0.1"]
  bridge VIA repl; ["0.0.1"]
  "Run a function by name with an argument. !! Target module must be manually built with `lake build` !! Flat ~200ms overhead to import everything dynamically (the withImportModules monad)"

  ARGS:
    module : String; "Module to import the function from."
    -- printResult : Bool; "Whether to print the output."
]


unsafe def main (args : List String) : IO UInt32 := do
  bridge.validate args
