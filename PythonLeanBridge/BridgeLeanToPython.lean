import Lean
import Lean.CoreM
import Lean.Data.Json
import Init.Prelude
import Init.Classical
import Cli
import Std

open Lean System IO Cli Elab Json Meta Elab Command Term Meta

def separator : String := "1498708047921580983"

def config (executable : String := "python") : IO.Process.SpawnArgs :=
  { cmd := executable
  , args := #["bridge_lean_to_python.py"]
  , cwd := some "lean_python_bridge/" -- TODO: make this settable (or combine Lean and Python into a single package somehow?)
  , stdout := .piped
  , stderr := .null
  , stdin := .piped
  }

-- What we keep around for the whole session. -/
structure SubprocSession where
  child : IO.Process.Child config.toStdioConfig
  term  : String

/-- Rolling buffer for partial reads. -/
structure SubprocState where
  buf : String := ""

abbrev PythonM := ReaderT SubprocSession (StateT SubprocState IO)

instance : Monad PythonM where
  pure := ReaderT.pure
  bind := ReaderT.bind

instance : Inhabited (PythonM α) where
  default := fun _ _ => throw default

/-- Run a `PythonM` action by spawning the process once and cleaning up. -/
partial def PythonM.run (act : PythonM α) (executable : String := "python") : IO α := do
  let child ← IO.Process.spawn (config executable)
  let sess  := SubprocSession.mk child separator
  let s0    := SubprocState.mk ""

  -- ensure cleanup even on exceptions
  try
    let (a, _) ←  (act sess).run s0
    pure a
  finally
    child.stdin.putStrLn "\n"
    child.stdin.flush
    pure ()

/-- Send a line to the child (optionally add a trailing newline). -/
def send (s : String) : PythonM Unit := do
  if s.contains '\n' then
    throw (IO.userError "send: no newlines allowed in message")
  if s.isEmpty then
    throw (IO.userError "send: no empty messages allowed")
  let h := (← read).child.stdin
  h.putStr s
  h.putStr "\n"
  h.flush

/-- Internal: read a chunk from stdout and append to the rolling buffer. -/
def readChunk : PythonM Unit := do
  let h := (← read).child.stdout
  let bytes ← h.read 1
  if bytes.size == 0 then
    pure ()  -- EOF
  else
    if h : (String.validateUTF8 bytes = true) then
      let chunk := String.fromUTF8 bytes h
      modify (fun st => { st with buf := st.buf ++ chunk })

/-- Receive one message, stopping at the session’s terminator.
    Leaves any extra bytes after the terminator in the buffer for next time. -/
partial def recvUntil : PythonM (List String) := do
  let term := (← read).term
  let st ← get
  let parts := st.buf.splitOn "\n"

  -- Look for the terminator that tells us a command has been fully executed and its value returned
  if parts.contains term then
    let idx := parts.idxOf term
    -- If there's nothing to return, discard the terminator and continue
    if idx == 0 then
      set { st with buf := String.intercalate "\n" parts.tail! }
      readChunk
      recvUntil
    -- Otherwise, return everything that's been output during the command
    else
      let ⟨out, rest⟩   := parts.splitAt idx
      set { st with buf := String.intercalate "\n" rest }
      pure out
  else
    readChunk
    recvUntil

/-- Convenience: send then wait for one response. -/
def sendAndReceive (s : String) : PythonM String := do
  send s
  return (← recvUntil).getLast!

/-- Optional: end the session early by closing stdin and returning the exit code. -/
def close : PythonM Unit := do
  let child := (← read).child
  child.stdin.putStrLn "\n"
  child.stdin.flush
  -- Child will close itself after receiving an empty line

class PythonType (α : Type) where
  repr : String
  fromrepr : String → PythonM α
  torepr : α → String

instance : PythonType String where
  repr := "str"
  fromrepr s := do return s
  torepr m := "\"" ++ m ++ "\""

instance : PythonType Int where
  repr := "int"
  fromrepr s := do match s.toInt? with
    | some n => return n
    | none => throw (IO.userError s!"PythonType.Int: expected int, got '{s}'")
  torepr m := m.repr

instance : PythonType Nat where
  repr := "int"
  fromrepr s := do match s.toNat? with
  | some n => return n
  | none => throw (IO.userError s!"PythonType.Nat: expected nat, got '{s}'")
  torepr m := m.repr

instance : PythonType Float where
  repr := "float"
  fromrepr s := if let some s := Json.parse s |>.toOption.bind (Json.getNum? · |>.toOption) then
    return s.toFloat
  else
    throw (IO.userError s!"PythonType.Float: expected float, got '{s}'")
  torepr m := m.toString

instance : PythonType Bool where
  repr := "bool"
  fromrepr s := do
    if s == "True" then return true
    else if s == "False" then return false
    else throw (IO.userError s!"PythonType.Bool: expected 'True' or 'False', got '{s}'")
  torepr m :=
    if m then "True"
    else "False"

instance : PythonType Unit where
  repr := "NoneType"
  fromrepr _ := do return ()
  torepr _ :="None"

def commandResult {α : Type} [PyType : PythonType α] (statement : String) : PythonM α := do
  let payload : Json := Json.mkObj
    [ ("statement", Json.str statement)
    , ("type", Json.str PyType.repr)
    , ("run_method", if PyType.repr == "NoneType" then Json.str "exec" else Json.str "eval")
    ]
  let res ← sendAndReceive (Json.compress payload)

  let ⟨type, value⟩ ← match Json.parse res |>.toOption with
    | some parsed =>
      match (((parsed.getObjVal? "type").bind Json.getStr? |>.toOption), ((parsed.getObjVal? "value").bind Json.getStr? |>.toOption)) with
        | (some type, some value) => pure (type, value)
        | _ => throw (IO.userError s!"Internal error: malformed JSON received from Python. Expected 'type' and 'value' fields. You shouldn't be seeing this; if you are, tell Tate and he'll fix it.")
    | _ => throw (IO.userError s!"Internal error: malformed JSON received from Python. You shouldn't be seeing this; if you are, tell Tate and he'll fix it.")

  if type == "Error" then
    throw (IO.userError s!"Python encountered an error:\n{value}")

  PyType.fromrepr value

def PythonM.toOption (m : PythonM α) : IO (Option α) := do
  try
    let res ← m.run
    pure (some res)
  catch _ =>
    pure none



namespace ArgsList

structure ArgsList where
  args : List String

def nil : ArgsList := { args := [] }

def cons {α : Type} (arg : α) [pytype : PythonType α] (args : ArgsList) : ArgsList :=
{ args := (pytype.torepr arg) :: args.args }

end ArgsList


namespace PythonObject

class PythonObject where
  handle : String

instance : PythonType PythonObject where
  repr := "object"
  fromrepr s := do
    pure { handle := s }
  torepr obj := obj.handle

def get {α : Type} (obj : PythonObject) (attr : String) [PythonType α] : PythonM α := do
  commandResult (s!"{obj.handle}.{attr}")

def set {α : Type} [type : PythonType α] (obj : PythonObject) (attr : String) (value : α) : PythonM Unit := do
  commandResult (s!"{obj.handle}.{attr} = {type.torepr value}")
  -- return obj

def call {α : Type} [PythonType α] (obj : PythonObject) (args : ArgsList.ArgsList) : PythonM α := do
  let args_str := String.intercalate ", " args.args
  commandResult (s!"{obj.handle}({args_str})")

def toString (obj : PythonObject) : PythonM String := do
  commandResult (s!"str({obj.handle})")

-- Function call: like mypythonfunction(arg1, "arg2", 3)
macro pyobj:term "(" xs:term,* ")" : term => do
  let mut acc ← `(ArgsList.nil)
  for x in xs.getElems.reverse do
    acc ← `(ArgsList.cons $x $acc)
  return Syntax.mkCApp ``PythonObject.call #[pyobj, acc]

-- elab pyobj:term "." attr:term : term => do
--   let elab_py ← elabTermEnsuringType pyobj (some (Expr.const ``PythonObject []))
--   let elab_attr ← elabTermEnsuringType attr (some (Expr.const ``String []))
--   return Expr.app (Expr.app (Expr.const ``PythonObject.get []) elab_py) elab_attr
  -- return Expr.app (Expr.const ``PythonObject.get []) elab_py




syntax (name := setattr) term "." term (" : " term)? " := " term : term

-- Credit to Aaron for helping me with annoying instance stuff
@[term_elab setattr]
def setattr_impl : TermElab := fun stx expectedType? => do
  let pyobj := stx[0]
  let attr := stx[2]
  let type?? := stx[3][1]
  let type? := if type??.isMissing then none else some type??
  let value := stx[5]
  -- tryPostponeIfNoneOrMVar expectedType?
  -- let some expectedType := expectedType? | throwError "expected type must be known"
  -- if expectedType.isMVar then
  --   throwError "expected type must be known"

  let elab_py ← elabTermEnsuringType pyobj (some (Expr.const ``PythonObject []))
  let elab_type? ← type?.mapM fun type => elabTermEnsuringType type[1] (some (.sort (.succ .zero)))
  let elab_attr ← elabTermEnsuringType attr (some (Expr.const ``String []))
  let elab_value ← elabTerm value elab_type?

  synthesizeSyntheticMVarsNoPostponing


  let instType : Expr := .app (.const ``PythonType []) (← inferType elab_value)
  let inst ← synthInstance instType
  return mkApp5 (.const ``PythonObject.set []) (← inferType elab_value) inst elab_py elab_attr elab_value





syntax (name := getattr) term "." term : term

-- Credit to Aaron for helping me with annoying instance stuff
@[term_elab getattr]
def getattr_impl : TermElab := fun stx expectedType? => do
  let pyobj := stx[0]
  let attr := stx[2]
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType? | throwError "expected type must be known"
  if expectedType.isMVar then
    throwError "expected type must be known"
  if !(expectedType.isApp) then
    throwError s!"actually was {expectedType} ({expectedType.appArg!})"

  let elab_py ← elabTermEnsuringType pyobj (some (Expr.const ``PythonObject []))
  let elab_attr ← elabTermEnsuringType attr (some (Expr.const ``String []))

  -- let elab_attr ← mkAppM ``String #[attr]
  -- elab_py.stri

  let instType : Expr := .app (.const ``PythonType []) expectedType.appArg!
  let inst ← synthInstance instType
  return mkApp4 (.const ``PythonObject.get []) expectedType.appArg! elab_py elab_attr inst

end PythonObject
