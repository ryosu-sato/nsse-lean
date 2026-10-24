import NSSE.CertifiedStructuralEmitter
import NSSE.ForestWordAttachment

/-!
# Emitting a hub geometry from two forest occurrences

Two concrete child occurrences in one positioned forest, with equal
literal yields and strictly ordered starts, supply all fields required
by `TranslationHubGeometry`.
-/

namespace NSSE

universe u

structure ForestTranslationPair (α : Type u) where
  left : Word α
  forest : List (FactorTree α)
  right : Word α
  first : ForestOccurrence α forest
  second : ForestOccurrence α forest
  starts_lt :
    (first.interval left).start < (second.interval left).start
  yields_equal : first.child.yield = second.child.yield

namespace ForestTranslationPair

def upper (pair : ForestTranslationPair α) : Word α :=
  pair.left ++ FactorTree.forestYield pair.forest ++ pair.right

def parent (pair : ForestTranslationPair α) : NatInterval :=
  forestParentInterval pair.left pair.forest
    pair.first.forestYield_nonempty

def hubGeometry
    (pair : ForestTranslationPair α)
    (C : ControlMonoid Wire) (letter : α → Wire) :
    TranslationHubGeometry α C letter where
  word := pair.upper
  start := (pair.first.interval pair.left).start
  shift :=
    (pair.second.interval pair.left).start -
      (pair.first.interval pair.left).start
  factorLength := pair.first.child.yield.length
  shift_positive := Nat.sub_pos_of_lt pair.starts_lt
  factor_nonempty :=
    List.length_pos_iff.mpr
      (FactorTree.yield_ne_nil pair.first.wellFormed)
  in_bounds := by
    have hsecond :=
      pair.second.contained pair.left
    have hparent :
        pair.parent.stop ≤ pair.upper.length := by
      simp [parent, upper, forestParentInterval]
    have hlength :
        pair.first.child.yield.length =
          pair.second.child.yield.length :=
      congrArg List.length pair.yields_equal
    calc
      (pair.first.interval pair.left).start +
            ((pair.second.interval pair.left).start -
              (pair.first.interval pair.left).start) +
          pair.first.child.yield.length =
          (pair.second.interval pair.left).start +
            pair.first.child.yield.length := by
              rw [Nat.add_sub_of_le
                (Nat.le_of_lt pair.starts_lt)]
      _ = (pair.second.interval pair.left).start +
            pair.second.child.yield.length := by rw [hlength]
      _ = (pair.second.interval pair.left).stop := rfl
      _ ≤ pair.parent.stop := by
        simpa [parent, forestParentInterval] using hsecond.2
      _ ≤ pair.upper.length := hparent
  factors_equal := by
    have hshift :
        (pair.first.interval pair.left).start +
            ((pair.second.interval pair.left).start -
              (pair.first.interval pair.left).start) =
          (pair.second.interval pair.left).start := by
      exact Nat.add_sub_of_le (Nat.le_of_lt pair.starts_lt)
    rw [hshift]
    calc
      Word.factor pair.upper
          (pair.first.interval pair.left).start
          pair.first.child.yield.length =
          pair.first.child.yield := by
            exact pair.first.factor_in_context_eq_yield
              pair.left pair.right
      _ = pair.second.child.yield := pair.yields_equal
      _ = Word.factor pair.upper
          (pair.second.interval pair.left).start
          pair.second.child.yield.length := by
            symm
            exact pair.second.factor_in_context_eq_yield
              pair.left pair.right
      _ = Word.factor pair.upper
          (pair.second.interval pair.left).start
          pair.first.child.yield.length := by
            rw [congrArg List.length pair.yields_equal]

def contextualEmitter
    (pair : ForestTranslationPair α)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ContextualStructuralEmitter α Wire C letter predicateCount
      Ctl Cut Macro where
  emitter := .hub (pair.hubGeometry C letter)
  context :=
    { control := control
      cut := cut
      lca := pair.parent
      macroData := macroData }

theorem contextualEmitter_nonidentity
    (pair : ForestTranslationPair α)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ¬ IdentityLoop
      (StructuralLoopStep.oneStepExecution
        (pair.contextualEmitter C letter control cut macroData :
          ContextualStructuralEmitter α Wire C letter predicateCount
            Ctl Cut Macro).emitter.sourceState
        (pair.contextualEmitter C letter control cut macroData :
          ContextualStructuralEmitter α Wire C letter predicateCount
            Ctl Cut Macro).emitter.emittedStep).summary :=
  (pair.hubGeometry C letter).emitted_nonidentity

def contextualEmitterChain
    (pair : ForestTranslationPair α)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ContextualStructuralEmitterChain α Wire C letter predicateCount
      Ctl Cut Macro
      (pair.contextualEmitter (predicateCount := predicateCount)
        C letter control cut macroData).emitter.sourceState
      [pair.contextualEmitter (predicateCount := predicateCount)
        C letter control cut macroData] :=
  .cons (pair.contextualEmitter (predicateCount := predicateCount)
      C letter control cut macroData)
    (.nil
      (pair.contextualEmitter (predicateCount := predicateCount)
        C letter control cut macroData
        ).emitter.targetState)

theorem contextualEmitterChain_endpoint_ne
    (pair : ForestTranslationPair α)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    (pair.contextualEmitterChain C letter control cut macroData :
      ContextualStructuralEmitterChain α Wire C letter predicateCount
        Ctl Cut Macro _ _).finalState ≠
      (pair.contextualEmitter (predicateCount := predicateCount)
        C letter control cut macroData
        ).emitter.sourceState := by
  have hnonidentity :=
    pair.contextualEmitter_nonidentity
      (predicateCount := predicateCount)
      C letter control cut macroData
  rw [LoopExecution.nonidentity_iff_endpoint_ne] at hnonidentity
  change
    StructuralLoopStep.advance
        (pair.contextualEmitter (predicateCount := predicateCount)
          C letter control cut macroData).emitter.sourceState
        (pair.contextualEmitter (predicateCount := predicateCount)
          C letter control cut macroData).emitter.emittedStep ≠
      (pair.contextualEmitter (predicateCount := predicateCount)
        C letter control cut macroData).emitter.sourceState
    at hnonidentity
  rw [(pair.contextualEmitter (predicateCount := predicateCount)
    C letter control cut macroData).emitter.advance_eq_target]
    at hnonidentity
  simpa [contextualEmitterChain,
    ContextualStructuralEmitterChain.finalState] using hnonidentity

end ForestTranslationPair

end NSSE
