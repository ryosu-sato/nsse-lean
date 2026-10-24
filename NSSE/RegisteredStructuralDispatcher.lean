import NSSE.FiniteLoopDispatcher
import NSSE.StructuralLoopSteps

/-!
# Registering structural emitters in the finite loop dispatcher

A concrete emitted step computes an actual `LoopSummary`.  Registration
assigns that summary one finite loop ID.  The emitted compiler tag carries
only the finite target wire and ID, while the dispatcher recovers the
summary through its lookup table.
-/

namespace NSSE

universe u

structure StructuralTagContext
    (Ctl Cut LCA Macro : Type u) where
  control : Ctl
  cut : Cut
  lca : LCA
  macroData : Macro

structure RegisteredStructuralStep
    (Wire LoopId : Type u) (width predicateCount : Nat)
    (summaryOf : LoopId → LoopSummary Wire) where
  source : NormalizedLoopState Wire width
  step : StructuralLoopStep Wire width predicateCount
  loopId : LoopId
  summary_registered :
    summaryOf loopId =
      (StructuralLoopStep.oneStepExecution source step).summary

namespace RegisteredStructuralStep

def label
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf) :
    FiniteLoopLabel Wire LoopId where
  wire := registered.step.targetWire
  loopId := registered.loopId

def emittedTag
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut LCA Macro) :
    FiniteLoopCompilerTag Ctl Cut Orientation LCA Macro
      Wire LoopId Atom (EuclideanSymbol predicateCount) :=
  match registered.step with
  | .nonstrong .. =>
      .nonstrong context.control context.cut context.lca
        context.macroData registered.label
  | .strong _ _ quotient =>
      .strong context.control context.cut context.macroData
        registered.label quotient
  | .hub .. =>
      .hub context.control context.cut context.macroData
        registered.label
  | .copy _ _ orientation =>
      .copy context.control context.cut orientation
        context.macroData registered.label

@[simp] theorem emittedTag_loopId
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut LCA Macro) :
    (registered.emittedTag (Atom := Atom) context).loopId? =
      some registered.loopId := by
  rcases registered with ⟨source, step, loopId, hregistered⟩
  cases step <;> rfl

@[simp] theorem emittedTag_kind
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut LCA Macro) :
    (registered.emittedTag (Atom := Atom) context).kind =
      registered.step.kind := by
  rcases registered with ⟨source, step, loopId, hregistered⟩
  cases step <;> rfl

theorem emittedTag_derives_iff_nonidentity
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq LCA] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId] [DecidableEq Atom]
    (summaryOf : LoopId → LoopSummary Wire)
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut LCA Macro)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (lca : Enumeration LCA) (macros : Enumeration Macro)
    (labels : Enumeration (FiniteLoopLabel Wire LoopId))
    (atom : Enumeration Atom)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ((finiteLoopRuleTests summaryOf).ruleSystem
      ctl cut orientation lca macros labels atom quotient
      ).TaggedDerives
        (registered.emittedTag (Atom := Atom) context) ↔
      ¬ IdentityLoop (summaryOf registered.loopId) := by
  rw [finiteLoop_taggedDerives_iff]
  constructor
  · rintro ⟨loopId, hloop, hnonidentity⟩
    rw [registered.emittedTag_loopId] at hloop
    cases Option.some.inj hloop
    exact hnonidentity
  · intro hnonidentity
    exact ⟨registered.loopId,
      registered.emittedTag_loopId context, hnonidentity⟩

theorem emittedTag_derives_iff_terminalHorn
    [DecidableEq Ctl] [DecidableEq Cut]
    [DecidableEq LCA] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId] [DecidableEq Atom]
    (summaryOf : LoopId → LoopSummary Wire)
    (registered :
      RegisteredStructuralStep Wire LoopId width predicateCount
        summaryOf)
    (context : StructuralTagContext Ctl Cut LCA Macro)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (lca : Enumeration LCA) (macros : Enumeration Macro)
    (labels : Enumeration (FiniteLoopLabel Wire LoopId))
    (atom : Enumeration Atom)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ((finiteLoopRuleTests summaryOf).ruleSystem
      ctl cut orientation lca macros labels atom quotient
      ).TaggedDerives
        (registered.emittedTag (Atom := Atom) context) ↔
      HornDerives
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            registered.source registered.step).summary).compiler
        (loopCompilerTerminalHornFamily
          (StructuralLoopStep.oneStepExecution
            registered.source registered.step).summary).root := by
  rw [registered.emittedTag_derives_iff_nonidentity
    summaryOf context ctl cut orientation lca macros labels
      atom quotient,
    registered.summary_registered,
    loopCompilerTerminalHornFamily_derives_iff,
    LoopUpdate.IsIdentity]

end RegisteredStructuralStep

end NSSE
