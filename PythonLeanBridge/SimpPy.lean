import Lean
import PythonLeanBridge.BridgeLeanToPython
import Mathlib.Analysis.SpecialFunctions.Integrals

open Lean Meta Tactic Elab Meta Term Tactic

axiom sympy_oracle (goal : Prop) : goal

elab "simp_py" : tactic =>
  withMainContext do
    let maingoal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← maingoal.getDecl
    let goalType := goalDecl.type
    let expr ← instantiateMVars goalType
    let mut goal := (← PrettyPrinter.ppExpr expr).pretty

    if goal.startsWith "∫ (" then
      goal := goal.stripPrefix "∫ ("
      let var := goal.get! 0
      goal := goal.stripPrefix s!"{var}"

      if goal.startsWith " : ℝ) in " then
        goal := goal.stripPrefix " : ℝ) in "
        let lower := goal.get! 0
        goal := goal.stripPrefix s!"{lower}"

        if goal.startsWith " .." then
          goal := goal.stripPrefix " .."
          let upper := goal.get! 0
          goal := goal.stripPrefix s!"{upper},"

          let mut ⟨function, target_val⟩ := (goal.splitOn " = " |>.get! 0, goal.splitOn " = " |>.get! 1)
          function := function.replace "^" "**"
          -- dbg_trace s!"integrating {var} from {lower} to {upper} with function {function} and target value {target_val}"

          let ok ← PythonM.run (executable := "/usr/local/Caskroom/miniconda/base/envs/LeanRAG/bin/python") do
            commandResult s!"from sympy import *"
            commandResult s!"init_printing(use_unicode=False)"
            commandResult s!"x = Symbol('{var}')"
            let ok : Bool ← commandResult s!"N(integrate({function}, ({var}, {lower}, {upper}))) == {target_val}"
            return ok

          if ok then
            maingoal.assign (← mkAppM ``sympy_oracle #[expr])
            return
    throwError "Couldn't solve goal :("
