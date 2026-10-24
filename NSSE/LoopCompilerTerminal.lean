import NSSE.LoopTransitionHornFamily
import NSSE.GlobalTerminalBridge

/-!
# Nonidentity loop updates in the VBRP terminal stratum

A normalized wire/counter update contains finite named-wire reuse and a
finite Parikh-style displacement vector.  It therefore occupies the VBRP
slot of `CompilerTerminal`; the other three strata are empty.
-/

namespace NSSE

universe u

abbrev LoopCompilerTerminal (Wire : Type u) :=
  CompilerTerminal
    (EmptyInput Wire) (EmptyInput Wire)
    (LoopUpdate Wire) (EmptyInput Wire)

def loopCompilerTerminal (update : LoopUpdate Wire) :
    LoopCompilerTerminal Wire :=
  .vbrp update

def decideLoopCompilerTerminal [DecidableEq Wire]
    (terminal : LoopCompilerTerminal Wire) : Bool :=
  decideTerminal
    (emptyExactSolver Wire)
    (emptyExactSolver Wire)
    loopNonidentitySolver
    (emptyExactSolver Wire)
    terminal

def LoopCompilerTerminalFormula [DecidableEq Wire]
    (terminal : LoopCompilerTerminal Wire) : Prop :=
  terminalFormula
    (emptyExactSolver Wire)
    (emptyExactSolver Wire)
    loopNonidentitySolver
    (emptyExactSolver Wire)
    terminal

theorem decideLoopCompilerTerminal_correct [DecidableEq Wire]
    (terminal : LoopCompilerTerminal Wire) :
    decideLoopCompilerTerminal terminal = true ↔
      LoopCompilerTerminalFormula terminal := by
  exact decideTerminal_correct
    (emptyExactSolver Wire)
    (emptyExactSolver Wire)
    loopNonidentitySolver
    (emptyExactSolver Wire)
    terminal

theorem loopCompilerTerminal_formula_iff
    [DecidableEq Wire] (update : LoopUpdate Wire) :
    LoopCompilerTerminalFormula (loopCompilerTerminal update) ↔
      ¬ update.IsIdentity := by
  rfl

theorem decide_loopCompilerTerminal_iff
    [DecidableEq Wire] (update : LoopUpdate Wire) :
    decideLoopCompilerTerminal (loopCompilerTerminal update) = true ↔
      ¬ update.IsIdentity := by
  rw [decideLoopCompilerTerminal_correct,
    loopCompilerTerminal_formula_iff]

def loopCompilerTerminalHornFamily [DecidableEq Wire]
    (update : LoopUpdate Wire) : HornFamily :=
  compilerTerminalHornFamily
    (emptyExactSolver Wire)
    (emptyExactSolver Wire)
    loopNonidentitySolver
    (emptyExactSolver Wire)
    (loopCompilerTerminal update)

theorem loopCompilerTerminalHornFamily_derives_iff
    [DecidableEq Wire] (update : LoopUpdate Wire) :
    HornDerives
        (loopCompilerTerminalHornFamily update).compiler
        (loopCompilerTerminalHornFamily update).root ↔
      ¬ update.IsIdentity := by
  exact compilerTerminalHornFamily_derives_iff
    (emptyExactSolver Wire)
    (emptyExactSolver Wire)
    loopNonidentitySolver
    (emptyExactSolver Wire)
    (loopCompilerTerminal update)

theorem decideLoopCompilerTerminalHornFamily_correct
    [DecidableEq Wire] (update : LoopUpdate Wire) :
    decideHornState
        (loopCompilerTerminalHornFamily update).compiler
        (loopCompilerTerminalHornFamily update).root = true ↔
      ¬ update.IsIdentity := by
  exact decideCompilerTerminalHornFamily_correct
    (emptyExactSolver Wire)
    (emptyExactSolver Wire)
    loopNonidentitySolver
    (emptyExactSolver Wire)
    (loopCompilerTerminal update)

theorem structuralTag_derives_iff_loopTerminal
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (update : LoopUpdate Wire)
    (hupdate : tag.loopUpdate? = some update) :
    (loopTransitionRuleTests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      decideLoopCompilerTerminal
        (loopCompilerTerminal update) = true := by
  rw [loop_taggedDerives_iff_nonidentity,
    decide_loopCompilerTerminal_iff]
  constructor
  · rintro ⟨found, hfound, hnonidentity⟩
    rw [hupdate] at hfound
    cases hfound
    exact hnonidentity
  · intro hnonidentity
    exact ⟨update, hupdate, hnonidentity⟩

theorem structuralTag_derives_iff_loopTerminalHorn
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (update : LoopUpdate Wire)
    (hupdate : tag.loopUpdate? = some update) :
    (loopTransitionRuleTests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      HornDerives
        (loopCompilerTerminalHornFamily update).compiler
        (loopCompilerTerminalHornFamily update).root := by
  rw [loop_taggedDerives_iff_nonidentity,
    loopCompilerTerminalHornFamily_derives_iff]
  constructor
  · rintro ⟨found, hfound, hnonidentity⟩
    rw [hupdate] at hfound
    cases hfound
    exact hnonidentity
  · intro hnonidentity
    exact ⟨update, hupdate, hnonidentity⟩

end NSSE
