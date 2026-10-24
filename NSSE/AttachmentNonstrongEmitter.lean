import NSSE.CertifiedStructuralEmitter
import NSSE.ForestWordAttachment

/-!
# Emitting a nonstrong step from attachment routing

The side branch of a word-bearing interval attachment already contains
all geometry required by `StrictChildNonstrongGeometry`.  This module
turns it into the common contextual emitter; the local branch retains
the exact primitive-periodic/mismatch-Horn response.
-/

namespace NSSE

universe u

def IntervalWordAttachment.nonstrongGeometry
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (delegation :
      SideDelegation attachment.parent child attachment.domains)
    (wireOf : NatInterval → Wire) :
    StrictChildNonstrongGeometry Wire where
  parent := attachment.parent
  child := child
  attachment := attachment.domains
  delegates := delegation
  wireOf := wireOf

def IntervalWordAttachment.nonstrongEmitter
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (delegation :
      SideDelegation attachment.parent child attachment.domains)
    (wireOf : NatInterval → Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ContextualStructuralEmitter α Wire C letter predicateCount
      Ctl Cut Macro :=
  ContextualStructuralEmitter.nonstrong
    (attachment.nonstrongGeometry delegation wireOf)
    control cut macroData

theorem IntervalWordAttachment.nonstrongEmitter_nonidentity
    (attachment : IntervalWordAttachment α)
    {child : NatInterval}
    (delegation :
      SideDelegation attachment.parent child attachment.domains)
    (wireOf : NatInterval → Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution
        (attachment.nonstrongEmitter delegation wireOf C letter
          control cut macroData :
          ContextualStructuralEmitter α Wire C letter predicateCount
            Ctl Cut Macro).emitter.sourceState
        (attachment.nonstrongEmitter delegation wireOf C letter
          control cut macroData :
          ContextualStructuralEmitter α Wire C letter predicateCount
            Ctl Cut Macro).emitter.emittedStep).summary := by
  exact
    (attachment.nonstrongGeometry delegation wireOf
      ).emitted_nonidentity

theorem IntervalWordAttachment.RoutingOutcome.emitter_or_periodic_or_mismatch
    [DecidableEq α]
    {attachment : IntervalWordAttachment α}
    {children : List NatInterval}
    (outcome : attachment.RoutingOutcome children)
    (wireOf : NatInterval → Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    (∃ (child : NatInterval)
        (delegation :
          SideDelegation attachment.parent child attachment.domains),
        child ∈ children ∧
        let emitter :
            ContextualStructuralEmitter α Wire C letter predicateCount
              Ctl Cut Macro :=
          attachment.nonstrongEmitter delegation wireOf C letter
            control cut macroData
        ¬ IdentityLoop
          (StructuralLoopStep.oneStepExecution
            emitter.emitter.sourceState
            emitter.emitter.emittedStep).summary) ∨
      (∃ root : Word α, ∃ m n : Nat,
        root.IsPrimitive ∧
        0 < m ∧
        attachment.payload = Word.power root m ∧
        attachment.orderedAttachment.middle = Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.orderedAttachment.left
          attachment.orderedAttachment.middle
          attachment.orderedAttachment.right
          attachment.payload).root := by
  cases outcome with
  | side child member delegation _ _ =>
      exact Or.inl
        ⟨child, delegation, member,
          attachment.nonstrongEmitter_nonidentity
            delegation wireOf C letter control cut macroData⟩
  | «local» _ ordered ordered_eq =>
      subst ordered
      exact Or.inr attachment.periodic_or_mismatchHorn

theorem ForestWordAttachment.emitter_or_periodic_or_mismatch
    [DecidableEq α]
    (attachment : ForestWordAttachment α)
    (children : List NatInterval)
    (wireOf : NatInterval → Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    (∃ (child : NatInterval)
        (delegation :
          SideDelegation attachment.parent child attachment.domains),
        child ∈ children ∧
        let emitter :
            ContextualStructuralEmitter α Wire C letter predicateCount
              Ctl Cut Macro :=
          attachment.toIntervalWordAttachment.nonstrongEmitter
            delegation wireOf C letter control cut macroData
        ¬ IdentityLoop
          (StructuralLoopStep.oneStepExecution
            emitter.emitter.sourceState
            emitter.emitter.emittedStep).summary) ∨
      (∃ root : Word α, ∃ m n : Nat,
        root.IsPrimitive ∧
        0 < m ∧
        attachment.payload = Word.power root m ∧
        attachment.toIntervalWordAttachment.orderedAttachment.middle =
          Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily
          attachment.toIntervalWordAttachment.orderedAttachment.left
          attachment.toIntervalWordAttachment.orderedAttachment.middle
          attachment.toIntervalWordAttachment.orderedAttachment.right
          attachment.payload).compiler
        (insertionSquareMismatchHornFamily
          attachment.toIntervalWordAttachment.orderedAttachment.left
          attachment.toIntervalWordAttachment.orderedAttachment.middle
          attachment.toIntervalWordAttachment.orderedAttachment.right
          attachment.payload).root := by
  exact
    (attachment.toIntervalWordAttachment.route children
      ).emitter_or_periodic_or_mismatch
        wireOf C letter control cut macroData

end NSSE
