import PythonLeanBridge.BridgeLeanToPython


def mini_example : IO Unit := do
  PythonM.run (executable := "python") do
    commandResult "import time"
    let r : Float ← commandResult "time.time()"
    IO.println s!"Current time is: {r}"

    -- IO.println <| (← commandResult "res" : String)

-- #eval mini_example





def computer_algebra_example : IO Unit := do
  PythonM.run (executable := "/usr/local/Caskroom/miniconda/base/envs/LeanRAG/bin/python") do
    commandResult "from sympy import *"
    commandResult "init_printing(use_unicode=True)"
    commandResult "x = Symbol('x')"

    let res : String ← commandResult "str(integrate(x**2 + x + 1, x))"
    IO.println s!"Integral of x^2 + x + 1 is: \n{res}"

-- #eval computer_algebra_example







set_option pp.rawOnError true
open PythonObject in
def test : IO Unit := do
  PythonM.run (executable := "/usr/local/Caskroom/miniconda/base/envs/LeanRAG/bin/python") do
    commandResult "class MyClass:\n   x = 1"
    let mut obj : PythonObject ← commandResult "MyClass()"
    IO.println <| (← toString obj) ++ "\n"

    let x : Nat ← obj."x"
    IO.println s!"x is assigned to {x}\n"

    obj."x" := 2

    let x : Nat ← obj."x"
    IO.println s!"x has been changed to {x}\n"



    commandResult "def python_add(arg1, arg2):\n  return arg1 + arg2"
    let func : PythonObject ← commandResult "python_add"
    let result : Nat ← func(1, 2)

    IO.println s!"Result of python_add(1, 2) is: {result}"


-- #eval test
