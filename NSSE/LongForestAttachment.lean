import NSSE.LongForestIdempotentNode
import NSSE.IdempotentNodeAttachment

/-!
# Extracting a concrete attachment from a long bounded forest

If the yielded word is longer than `2 ^ heightBound`, the forest
contains an idempotent node.  Its first two children and the contexts of
that node determine a `TwoForestAttachment` whose realized upper word is
exactly the original forest word.
-/

namespace NSSE

universe u v

namespace FactorTree.HeightBoundedForest

variable {M : Type v} {α : Type u}
variable {C : ControlMonoid M} {letter : α → M}
variable {word : Word α} {bound : Nat}

theorem exists_twoForestAttachment
    (forest : HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ []) :
    ∃ attachment : TwoForestAttachment α,
      attachment.toForestWordAttachment.upper = word := by
  obtain ⟨left, right, children, value, hword,
    hcount, hchildren, hvalue, hcontrols⟩ :=
    forest.exists_idempotent_context hlong
  let attachment :=
    firstTwoForestAttachment C letter children hcount hchildren
      left right payload hpayload
  refine ⟨attachment, ?_⟩
  rw [show
    attachment.toForestWordAttachment.upper =
      left ++ FactorTree.forestYield children ++ right by
        exact firstTwoForestAttachment_upper
          C letter children hcount hchildren
          left right payload hpayload]
  exact hword.symm

theorem exists_forestWordAttachment
    (forest : HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ []) :
    ∃ attachment : ForestWordAttachment α,
      attachment.upper = word := by
  obtain ⟨attachment, hupper⟩ :=
    forest.exists_twoForestAttachment hlong payload hpayload
  exact ⟨attachment.toForestWordAttachment, hupper⟩

theorem exists_attachment_completeCompilerResponse
    {Wire : Type u} {C : ControlMonoid Wire}
    {letter : α → Wire} {word : Word α} {bound : Nat}
    [DecidableEq α]
    (forest :
      HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ attachment : ForestWordAttachment α,
      attachment.upper = word ∧
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      (∃ emitter :
            ContextualStructuralEmitter α Wire C letter
              predicates.length Ctl Cut Macro,
            emitter.singletonChain.finalState ≠
              emitter.emitter.sourceState) ∨
          ordered.middle = [] ∨
          HornDerives
            (insertionSquareMismatchHornFamily
              ordered.left ordered.middle ordered.right
              attachment.payload).compiler
            (insertionSquareMismatchHornFamily
              ordered.left ordered.middle ordered.right
              attachment.payload).root) := by
  obtain ⟨left, right, children, value, hword,
    hcount, hchildren, hvalue, hcontrols⟩ :=
    forest.exists_idempotent_context hlong
  let two :=
    firstTwoForestAttachment C letter children hcount hchildren
      left right payload hpayload
  let attachment := two.toForestWordAttachment
  refine ⟨attachment, ?_, ?_⟩
  · rw [show attachment.upper =
        left ++ FactorTree.forestYield children ++ right by
      exact firstTwoForestAttachment_upper
        C letter children hcount hchildren
        left right payload hpayload]
    exact hword.symm
  · exact
      firstTwoForestAttachment_completeCompilerResponse
        C letter children hcount hchildren
        left right payload hpayload
        intervalChildren predicates wireOf strongWire
        control cut macroData

theorem exists_attachment_completeSemanticResponse
    {Wire : Type u} {C : ControlMonoid Wire}
    {letter : α → Wire} {word : Word α} {bound : Nat}
    [DecidableEq α]
    (forest :
      HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ attachment : ForestWordAttachment α,
      attachment.upper = word ∧
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      (∃ emitter :
            ContextualStructuralEmitter α Wire C letter
              predicates.length Ctl Cut Macro,
            emitter.singletonChain.finalState ≠
              emitter.emitter.sourceState) ∨
          ordered.middle = [] ∨
          Word.insertAt ordered.base attachment.payload
              ordered.leftSlot ≠
            Word.insertAt ordered.base attachment.payload
              ordered.rightSlot) := by
  obtain ⟨attachment, hupper, hresponse⟩ :=
    forest.exists_attachment_completeCompilerResponse
      hlong payload hpayload intervalChildren predicates
      wireOf strongWire control cut macroData
  refine ⟨attachment, hupper, ?_⟩
  dsimp only at hresponse ⊢
  rcases hresponse with hstructural | hempty | hmismatch
  · exact Or.inl hstructural
  · exact Or.inr (Or.inl hempty)
  · exact Or.inr (Or.inr
      ((attachment.toIntervalWordAttachment.orderedAttachment
        ).mismatchHorn_derives_iff.mp hmismatch))

theorem exists_attachment_insertionTrichotomy
    {Wire : Type u} {C : ControlMonoid Wire}
    {letter : α → Wire} {word : Word α} {bound : Nat}
    [DecidableEq α]
    (forest :
      HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ attachment : ForestWordAttachment α,
      attachment.upper = word ∧
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      (∃ emitter :
            ContextualStructuralEmitter α Wire C letter
              predicates.length Ctl Cut Macro,
            emitter.singletonChain.finalState ≠
              emitter.emitter.sourceState) ∨
          Word.insertAt ordered.base attachment.payload
              ordered.leftSlot =
            Word.insertAt ordered.base attachment.payload
              ordered.rightSlot ∨
          Word.insertAt ordered.base attachment.payload
              ordered.leftSlot ≠
            Word.insertAt ordered.base attachment.payload
              ordered.rightSlot) := by
  obtain ⟨attachment, hupper, hresponse⟩ :=
    forest.exists_attachment_completeSemanticResponse
      hlong payload hpayload intervalChildren predicates
      wireOf strongWire control cut macroData
  refine ⟨attachment, hupper, ?_⟩
  dsimp only at hresponse ⊢
  rcases hresponse with hstructural | hempty | hmismatch
  · exact Or.inl hstructural
  · have hequal :=
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).insertions_eq_of_middle_nil hempty
    exact Or.inr (Or.inl hequal)
  · exact Or.inr (Or.inr hmismatch)

theorem exists_attachment_structural_or_mismatch
    {Wire : Type u} {C : ControlMonoid Wire}
    {letter : α → Wire} {word : Word α} {bound : Nat}
    [DecidableEq α]
    (forest :
      HeightBoundedForest C letter word bound)
    (hlong : 2 ^ bound < word.length)
    (payload : Word α) (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ attachment : ForestWordAttachment α,
      attachment.upper = word ∧
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).middle ≠ [] ∧
      (let ordered :=
        attachment.toIntervalWordAttachment.orderedAttachment
      (∃ emitter :
            ContextualStructuralEmitter α Wire C letter
              predicates.length Ctl Cut Macro,
            emitter.singletonChain.finalState ≠
              emitter.emitter.sourceState) ∨
          Word.insertAt ordered.base attachment.payload
              ordered.leftSlot ≠
            Word.insertAt ordered.base attachment.payload
              ordered.rightSlot) := by
  obtain ⟨left, right, children, value, hword,
    hcount, hchildren, hvalue, hcontrols⟩ :=
    forest.exists_idempotent_context hlong
  let two :=
    firstTwoForestAttachment C letter children hcount hchildren
      left right payload hpayload
  let attachment := two.toForestWordAttachment
  have hmiddle :
      (attachment.toIntervalWordAttachment.orderedAttachment
        ).middle ≠ [] :=
    firstTwoForestAttachment_middle_ne_nil
      C letter children hcount hchildren
      left right payload hpayload
  have hresponse :=
    firstTwoForestAttachment_completeCompilerResponse
      C letter children hcount hchildren
      left right payload hpayload
      intervalChildren predicates wireOf strongWire
      control cut macroData
  refine ⟨attachment, ?_, hmiddle, ?_⟩
  · rw [show attachment.upper =
        left ++ FactorTree.forestYield children ++ right by
      exact firstTwoForestAttachment_upper
        C letter children hcount hchildren
        left right payload hpayload]
    exact hword.symm
  · dsimp only at hresponse ⊢
    rcases hresponse with hstructural | hempty | hmismatch
    · exact Or.inl hstructural
    · exact False.elim (hmiddle hempty)
    · exact Or.inr
        ((attachment.toIntervalWordAttachment.orderedAttachment
          ).mismatchHorn_derives_iff.mp hmismatch)

end FactorTree.HeightBoundedForest

end NSSE
