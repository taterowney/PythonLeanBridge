import PythonLeanBridge.BridgeLeanToPython
import PythonLeanBridge.SimpPy

import Mathlib.Analysis.SpecialFunctions.Integrals


def mini_example : IO Unit := do
  PythonM.run (executable := "python") do
    commandResult "import time"
    let r : Float ← commandResult "time.time()"
    IO.println s!"Current time is: {r}"


-- #eval mini_example


def sympy_example : IO Unit := do
  PythonM.run (executable := "/usr/local/Caskroom/miniconda/base/envs/LeanRAG/bin/python") do
    commandResult "from sympy import *"
    commandResult "init_printing(use_unicode=True)"
    commandResult "x = Symbol('x')"

    let res : String ← commandResult "str(integrate(x**2 + x + 1, (x, 0, 1)))"
    IO.println s!"Integral of x^2 + x + 1 is: \n{res}"

-- #eval sympy_example


open PythonObject in
def object_example : IO Unit := do
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

-- #eval object_example


example : ∫ x in (0:ℝ)..1, x ^ 2 = 1/3 := by
  simp_py

example : ∫ x in (0:ℝ)..1, x ^ 2 + x + 1 = 11/6 := by
  simp_py









-- some toy functions accessed in example.py

def testfn (arg : Nat) : IO Nat := do
  return arg + 1


def effectful (n : Nat) : IO Unit := do
  IO.println s!"Testing with {n}"
