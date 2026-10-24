import NSSE.LoopCompilerTerminal
import NSSE.ConcreteSOA
import NSSE.Synchronized

/-!
# Occurrence provenance for normalized structural loops

A structural loop certificate retains an actual marked suffix occurrence
in either the forward word or its theta orientation, together with the
normalized finite wire/counter summary.  Thus loop classification never
forgets the concrete named periodic witness from which the tag arose.
-/

namespace NSSE

universe u

structure OrientedOccurrenceLoop
    (α Wire : Type u) where
  theta : α → α
  orientation : Orientation
  row : CapComponent α
  word : Word α
  sourceWire : Wire
  targetWire : Wire
  displacement : List Int
  occurrence :
    MarkedOccurrence row (Word.orient theta orientation word)

namespace OrientedOccurrenceLoop

def summary (cycle : OrientedOccurrenceLoop α Wire) :
    LoopSummary Wire where
  sourceWire := cycle.sourceWire
  targetWire := cycle.targetWire
  displacement := cycle.displacement

theorem periodicWitness
    (cycle : OrientedOccurrenceLoop α Wire) :
    PeriodicWitness cycle.row
      (Word.orient cycle.theta cycle.orientation cycle.word) := by
  exact
    (periodicWitness_iff_markedOccurrence
      cycle.row
      (Word.orient cycle.theta cycle.orientation cycle.word)).2
      cycle.occurrence

theorem identity_or_VBRPTerminal
    [DecidableEq Wire] (cycle : OrientedOccurrenceLoop α Wire) :
    IdentityLoop cycle.summary ∨
      (PeriodicWitness cycle.row
          (Word.orient cycle.theta cycle.orientation cycle.word) ∧
        HornDerives
          (loopCompilerTerminalHornFamily cycle.summary).compiler
          (loopCompilerTerminalHornFamily cycle.summary).root) := by
  by_cases hidentity : IdentityLoop cycle.summary
  · exact Or.inl hidentity
  · exact Or.inr
      ⟨cycle.periodicWitness,
        (loopCompilerTerminalHornFamily_derives_iff
          cycle.summary).2 hidentity⟩

theorem nonidentity_has_periodicWitness_and_terminal
    [DecidableEq Wire] (cycle : OrientedOccurrenceLoop α Wire)
    (hnonidentity : ¬ IdentityLoop cycle.summary) :
    PeriodicWitness cycle.row
        (Word.orient cycle.theta cycle.orientation cycle.word) ∧
      HornDerives
        (loopCompilerTerminalHornFamily cycle.summary).compiler
        (loopCompilerTerminalHornFamily cycle.summary).root :=
  ⟨cycle.periodicWitness,
    (loopCompilerTerminalHornFamily_derives_iff
      cycle.summary).2 hnonidentity⟩

def nonstrongTag
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (lca : LCA)
    (macroData : Macro) :
    LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass :=
  .nonstrong control cut lca macroData cycle.summary

def strongTag
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro)
    (quotient : QClass) :
    LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass :=
  .strong control cut macroData cycle.summary quotient

def hubTag
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass :=
  .hub control cut macroData cycle.summary

def copyTag
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    LoopCompilerTag Ctl Cut Orientation LCA Macro Wire Atom QClass :=
  .copy control cut cycle.orientation macroData cycle.summary

@[simp] theorem nonstrongTag_loopUpdate
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (lca : LCA)
    (macroData : Macro) :
    (cycle.nonstrongTag
      (Ori := Ori) (Atom := Atom) (QClass := QClass)
      control cut lca macroData).loopUpdate? =
        some cycle.summary := rfl

@[simp] theorem strongTag_loopUpdate
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro)
    (quotient : QClass) :
    (cycle.strongTag
      (Ori := Ori) (LCA := LCA) (Atom := Atom)
      control cut macroData quotient).loopUpdate? =
        some cycle.summary := rfl

@[simp] theorem hubTag_loopUpdate
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    (cycle.hubTag
      (Ori := Ori) (LCA := LCA) (Atom := Atom) (QClass := QClass)
      control cut macroData).loopUpdate? =
        some cycle.summary := rfl

@[simp] theorem copyTag_loopUpdate
    (cycle : OrientedOccurrenceLoop α Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    (cycle.copyTag
      (LCA := LCA) (Atom := Atom) (QClass := QClass)
      control cut macroData).loopUpdate? =
        some cycle.summary := rfl

theorem structuralTag_derives_iff_VBRP
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (cycle : OrientedOccurrenceLoop α Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (hsummary : tag.loopUpdate? = some cycle.summary) :
    (loopTransitionRuleTests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      HornDerives
        (loopCompilerTerminalHornFamily cycle.summary).compiler
        (loopCompilerTerminalHornFamily cycle.summary).root :=
  structuralTag_derives_iff_loopTerminalHorn
    ctl cut ori lca macros wire atom quotient
    tag cycle.summary hsummary

theorem structuralTag_derivation_has_provenance
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (cycle : OrientedOccurrenceLoop α Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (hsummary : tag.loopUpdate? = some cycle.summary)
    (hderive :
      (loopTransitionRuleTests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag) :
    PeriodicWitness cycle.row
        (Word.orient cycle.theta cycle.orientation cycle.word) ∧
      HornDerives
        (loopCompilerTerminalHornFamily cycle.summary).compiler
        (loopCompilerTerminalHornFamily cycle.summary).root := by
  exact ⟨cycle.periodicWitness,
    (cycle.structuralTag_derives_iff_VBRP
      ctl cut ori lca macros wire atom quotient
      tag hsummary).1 hderive⟩

end OrientedOccurrenceLoop

end NSSE
