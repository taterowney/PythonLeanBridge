import Batteries.Lean.HashSet
import Batteries.Data.List.Basic
import Batteries.Lean.HashMap
import Cli
import Lean
import Lean.CoreM
import Lean.Expr
import PythonLeanBridge.Frontend

open Lean Core Elab IO Meta Term Command Tactic Cli System String

set_option autoImplicit true



structure ExternalContext where
  name : Name
  kind : String
  module : Name
  text : String
  parent : CompilationStep
  pos : Option Pos := none
  endPos : Option Pos := none


instance : BEq ExternalContext where
  beq a b := a.name == b.name
  && a.kind.trim == b.kind.trim
  && a.module == b.module
  && a.text.trim == b.text.trim
  && a.parent.src.trim == b.parent.src.trim
  && a.parent.stx == b.parent.stx
  && a.pos == b.pos
  && a.endPos == b.endPos

-- From Mathlib.Lean.CoreM
def CoreM.withImportModules {α : Type} (modules : Array Name) (run : CoreM α)
    (searchPath : Option Lean.SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map (Import.mk · false)) options trustLevel fun env =>
    let ctx := {fileName, options, fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      run

-- From ImportGraph.RequiredModules
namespace Lean

/-- Return the name of the module in which a declaration was defined. -/
def Environment.getModuleFor? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | none =>
    if env.constants.map₂.contains declName then
      env.header.mainModule
    else
      none
  | some idx => env.header.moduleNames[idx.toNat]!
end Lean

partial def Lean.Expr.explicitConstants : Expr → MetaM NameSet
| .app f x => do
  -- We wrap with `try?` here because on tiny fraction of declarations in Mathlib,
  -- e.g. `Computation.exists_of_mem_parallel`, this fails with an error like
  -- `function expected ?m.88 ?m.93`.
  -- match (← try? (inferType f)) with TODO: how does this work in 4.16?
  match (some (← (inferType f))) with
  | some (.forallE _ _ _ .default) => return (← f.explicitConstants) ++ (← x.explicitConstants)
  | _ => f.explicitConstants
| .lam _ t b _ => do b.instantiate1 (← mkFreshExprMVar t) |>.explicitConstants
| .forallE _ t b _ => do b.instantiate1 (← mkFreshExprMVar t) |>.explicitConstants
| .letE n t v b _ => return (← v.explicitConstants)
    ++ (← withLetDecl n t v fun fvar => (b.instantiate1 fvar).explicitConstants)
| .const n _ => return NameSet.empty.insert n
| .mdata _ e => e.explicitConstants
| _ => return NameSet.empty

def getExplicitConstantsAsSet (t : TacticInfo) : MetaM (List Name) := do
  let set ← t.goalsBefore
    |>.filterMap t.mctxAfter.getExprAssignmentCore?
    |>.mapM Expr.explicitConstants

  let out : NameSet := set.foldl .union .empty
  let out2 : List Name := out.toList
  return out2


partial def go (s : Syntax) (acc : Array (Name × Option Pos × Option Pos)) : Array (Name × Option Pos × Option Pos) :=
  match s with
  | Syntax.ident _ _ name _ => acc.push (name, s.getPos?, s.getTailPos?)
  | Syntax.node _ _ args => args.foldl (fun acc s' => go s' acc) acc
  | _ => acc

def getConstants (step : CompilationStep) : MetaM (List (Name × Option Pos × Option Pos)) := do
  let idents := go step.stx #[]
  return idents.toList

def getUsedConstantsAsSet (t : TacticInfo) : NameSet :=
  let set := t.goalsBefore
    |>.filterMap t.mctxAfter.getExprAssignmentCore?
    |>.map Expr.getUsedConstantsAsSet
    -- |>.map Expr
    |>.foldl .union .empty

  set


def getKind' (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def getKind (const_map : ConstMap) (m : Name) : String :=
  let local_const := const_map.map₂
  let ext_const := const_map.map₁
  let c := local_const.find? m
  match c with
  | none => match ext_const[m]? with
    | some d => getKind' d
      -- | .axiomInfo _ => "axiom"
      -- | .defnInfo _ => "def"
      -- | .thmInfo _ => "theorem"
      -- | .opaqueInfo _ => "opaque"
      -- | .quotInfo _ => "quot"
      -- | .inductInfo _ => "inductive"
      -- | .ctorInfo _ => "constructor"
      -- | .recInfo _ => "recursor"
    | none => "Not Found"
  | some c => getKind' c --match c with
    -- | .axiomInfo _ => "axiom (internal)"
    -- | .defnInfo _ => "def (internal)"
    -- | .thmInfo _ => "theorem (internal)"
    -- | .opaqueInfo _ => "opaque (internal)"
    -- | .quotInfo _ => "quot (internal)"
    -- | .inductInfo _ => "inductive (internal)"
    -- | .ctorInfo _ => "constructor (internal)"
    -- | .recInfo _ => "recursor (internal)"

def isAuxLemma : Name → Bool
| .num (.str _ "_auxLemma") _ => true
| _ => false

def getContext (step:CompilationStep)
  (allowed_kinds : List String := ["theorem", "def","theorem (internal)", "def (internal)"] )
  : IO (List ExternalContext) := do

  let pf_env := step.commandStateBefore.env

  let ctx : Core.Context := {fileName := "", fileMap := default}
  let state : Core.State := {env := pf_env}

  let constants ← MetaM.toIO (getConstants step) ctx state
  let constants := constants.1.eraseDups


  let modules := constants.map (fun (c, pos, endPos) => (c, pos, endPos, pf_env.getModuleFor? c |>.getD (Name.anonymous)))

  let consts_mods_kind := modules.map (fun (c, pos, endPos, m) => (c, pos, endPos, m, getKind pf_env.constants c))

  let mods := (modules.map fun x => x.2.2.2) |>.eraseDups |>.filter fun m => m != Name.anonymous

  -- let allowed_kinds := ["theorem", "def","theorem (internal)", "def (internal)"]
  let constant_info ← CoreM.withImportModules mods.toArray do
    let mut out := []
    for (c, pos, endPos, module, kind) in consts_mods_kind do
      -- IO.println s!"{c}: {module.isAnonymous}"

      -- IO.println pf_env.constants.toList.length
      -- IO.println (pf_env.constants.find! `LeanRAG.Test.test).name
      -- IO.println "\n"
      if isAuxLemma c || kind ∉ allowed_kinds || module.isAnonymous then
        continue
      -- IO.println s!"extracting {c}, {module}"
      let rgs := ((← findDeclarationRanges? c).getD default).range
      -- let module := ((pf_env.getModuleFor? c).getD (Name.anonymous))
      -- IO.println s!"rg: {rgs.pos} -> {rgs.endPos}"
      let modulePath ← findLean module
      let fileContents ← IO.FS.readFile modulePath.toString
      -- get the source code within range
      let declTextList := if rgs.pos.line == 0 then [] else
        fileContents.splitOn "\n"
          |>.drop (rgs.pos.line - 1)
          |>.take (rgs.endPos.line - rgs.pos.line + 1)
      let declText := "\n".intercalate declTextList

      out := (ExternalContext.mk c kind module declText step pos endPos)::out
    return out
  let contexts := constant_info.eraseDups
  return contexts

-- open Elab.IO in
-- def test (targetModule : Name) (decls : Option (List Name)) (proofAsSorry? : Bool) (theoremsOnly : Bool := true) : IO Unit := do

--   searchPathRef.set compile_time_search_path%
--   let fileName := (← findLean targetModule).toString

--   /- Replace all tactics with "sorry" for faster execution -/
--   let proofAsSorry := ({} : KVMap).insert `debug.byAsSorry (.ofBool true)
--     |>.insert `linter.unusedVariables (.ofBool false)
--     |>.insert `linter.unusedTactic (.ofBool false)
--     |>.insert `linter.unreachableTactic (.ofBool false)

--   let options := if proofAsSorry? then proofAsSorry else {}
--   let steps := processInput' (← moduleSource targetModule) none options fileName
--   let targets := steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)

--   -- let mut results : Array Result := #[]

--   for (cmd, ci) in targets do
--     let ci_name_stem := ci.name.toString.splitOn "." |>.getLast! |>.toName
--     if (decls.isSome && !((decls.get!.contains ci_name_stem) || decls.get!.contains ci.name)) then
--       continue

--     let env := cmd.after
--     let name := ci.name
--     let isThm := match ci with
--       | .thmInfo _ => "theorem"
--       | .defnInfo _ => "definition"
--       | _ => "other"

--     let deps ← getContext cmd
--     IO.println s!"{ci.name}:"
--     for d in deps do
--       IO.println s!"{d.name}: {d.kind} in {d.module} at {d.pos.getD 0} to {d.endPos.getD 0}"
--     IO.println "\n"


-- #eval test `LeanRAG.Test none false
