import NSSE.HornFamilyCompiler
import NSSE.TaggedCompiler

/-!
# Exact solvers as Horn compiler families

Every accepted input of an exact terminal solver becomes a two-state
terminal-to-root Horn compiler.  The construction applies uniformly to
the four stratified compiler terminal sorts.
-/

namespace NSSE

universe u

def solverHornRule : HornRule where
  parent := 1
  children := [0]

def solverHornCompiler
    (solver : ExactSolver Input) (input : Input) :
    FiniteHornCompiler where
  stateCount := 2
  terminal := fun state =>
    if state = 0 then solver.decide input else false
  rules := [solverHornRule]

theorem decideSolverHornTerminal
    (solver : ExactSolver Input) (input : Input) :
    decideHornState (solverHornCompiler solver input) 0 =
      solver.decide input := by
  simp [decideHornState, solverHornCompiler, hornInitial,
    iterateMask, hornUpdate, hornBuild, hornNewBit, hornFires,
    allMaskBits, solverHornRule, maskBit, decideLeastFixedPoint]

theorem decideSolverHornRoot
    (solver : ExactSolver Input) (input : Input) :
    decideHornState (solverHornCompiler solver input) 1 =
      solver.decide input := by
  simp [decideHornState, solverHornCompiler, hornInitial,
    iterateMask, hornUpdate, hornBuild, hornNewBit, hornFires,
    allMaskBits, solverHornRule, maskBit, decideLeastFixedPoint]

theorem solverHorn_terminal_derives_iff
    (solver : ExactSolver Input) (input : Input) :
    HornDerives (solverHornCompiler solver input) 0 ↔
      solver.formula input := by
  rw [← solver.correct input,
    ← decideSolverHornTerminal,
    decideHornState_correct
      (solverHornCompiler solver input) 0 (by
        simp [solverHornCompiler])]

theorem solverHorn_root_derives_iff
    (solver : ExactSolver Input) (input : Input) :
    HornDerives (solverHornCompiler solver input) 1 ↔
      solver.formula input := by
  rw [← solver.correct input,
    ← decideSolverHornRoot,
    decideHornState_correct
      (solverHornCompiler solver input) 1 (by
        simp [solverHornCompiler])]

def exactSolverHornFamily
    (solver : ExactSolver Input) (input : Input) : HornFamily where
  compiler := solverHornCompiler solver input
  root := 1
  root_lt := by simp [solverHornCompiler]

theorem exactSolverHornFamily_derives_iff
    (solver : ExactSolver Input) (input : Input) :
    HornDerives
        (exactSolverHornFamily solver input).compiler
        (exactSolverHornFamily solver input).root ↔
      solver.formula input :=
  solverHorn_root_derives_iff solver input

def compilerTerminalSolver
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic) :
    ExactSolver
      (CompilerTerminal PWE PEL VBRP FixedPeriodic) where
  formula := terminalFormula pwe pel vbrp periodic
  decide := decideTerminal pwe pel vbrp periodic
  correct := decideTerminal_correct pwe pel vbrp periodic

def compilerTerminalHornFamily
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic)
    (terminal : CompilerTerminal PWE PEL VBRP FixedPeriodic) :
    HornFamily :=
  exactSolverHornFamily
    (compilerTerminalSolver pwe pel vbrp periodic) terminal

theorem compilerTerminalHornFamily_derives_iff
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic)
    (terminal : CompilerTerminal PWE PEL VBRP FixedPeriodic) :
    HornDerives
        (compilerTerminalHornFamily
          pwe pel vbrp periodic terminal).compiler
        (compilerTerminalHornFamily
          pwe pel vbrp periodic terminal).root ↔
      terminalFormula pwe pel vbrp periodic terminal :=
  exactSolverHornFamily_derives_iff
    (compilerTerminalSolver pwe pel vbrp periodic) terminal

theorem decideCompilerTerminalHornFamily_correct
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP)
    (periodic : ExactSolver FixedPeriodic)
    (terminal : CompilerTerminal PWE PEL VBRP FixedPeriodic) :
    decideHornState
        (compilerTerminalHornFamily
          pwe pel vbrp periodic terminal).compiler
        (compilerTerminalHornFamily
          pwe pel vbrp periodic terminal).root = true ↔
      terminalFormula pwe pel vbrp periodic terminal := by
  rw [decideHornState_correct
    (compilerTerminalHornFamily
      pwe pel vbrp periodic terminal).compiler
    (compilerTerminalHornFamily
      pwe pel vbrp periodic terminal).root
    (compilerTerminalHornFamily
      pwe pel vbrp periodic terminal).root_lt]
  exact compilerTerminalHornFamily_derives_iff
    pwe pel vbrp periodic terminal

end NSSE
