import NSSE.BoundedFactorForestAssembly
import NSSE.ForestWordAttachment
import NSSE.CompleteAttachmentResponse

/-!
# Extracting an attachment from an idempotent forest node

An idempotent Simon node has at least three well-formed forest children.
Its first two children give canonical distinct forest occurrences and
therefore a concrete `TwoForestAttachment`.
-/

namespace NSSE

universe u v

def firstTwoForestAttachment
    (C : ControlMonoid M) (letter : α → M)
    (children : List (FactorTree α))
    (hcount : 3 ≤ children.length)
    (hforests :
      ∀ tree ∈ children, FactorTree.IsForest C letter tree)
    (left right payload : Word α)
    (hpayload : payload ≠ []) :
    TwoForestAttachment α := by
  cases children with
  | nil => simp at hcount
  | cons first tail =>
      cases tail with
      | nil => simp at hcount
      | cons second tail =>
          cases tail with
          | nil => simp at hcount
          | cons third rest =>
              have hfirstForest :
                  FactorTree.IsForest C letter first :=
                hforests first (by simp)
              have hsecondForest :
                  FactorTree.IsForest C letter second :=
                hforests second (by simp)
              exact {
                left := left
                forest := first :: second :: third :: rest
                right := right
                payload := payload
                payload_nonempty := hpayload
                first := {
                  before := []
                  child := first
                  after := second :: third :: rest
                  decomposition := rfl
                  wellFormed :=
                    FactorTree.isForest_wellFormed C letter hfirstForest
                }
                second := {
                  before := [first]
                  child := second
                  after := third :: rest
                  decomposition := rfl
                  wellFormed :=
                    FactorTree.isForest_wellFormed C letter hsecondForest
                }
              }

theorem firstTwoForestAttachment_upper
    (C : ControlMonoid M) (letter : α → M)
    (children : List (FactorTree α))
    (hcount : 3 ≤ children.length)
    (hforests :
      ∀ tree ∈ children, FactorTree.IsForest C letter tree)
    (left right payload : Word α)
    (hpayload : payload ≠ []) :
    (firstTwoForestAttachment C letter children hcount hforests
      left right payload hpayload).toForestWordAttachment.upper =
        left ++ FactorTree.forestYield children ++ right := by
  cases children with
  | nil => simp at hcount
  | cons first tail =>
      cases tail with
      | nil => simp at hcount
      | cons second tail =>
          cases tail with
          | nil => simp at hcount
          | cons third rest =>
              rfl

theorem firstTwoForestAttachment_parentWord
    (C : ControlMonoid M) (letter : α → M)
    (children : List (FactorTree α))
    (hcount : 3 ≤ children.length)
    (hforests :
      ∀ tree ∈ children, FactorTree.IsForest C letter tree)
    (left right payload : Word α)
    (hpayload : payload ≠ []) :
    ((firstTwoForestAttachment C letter children hcount hforests
      left right payload hpayload).toForestWordAttachment
        ).toIntervalWordAttachment.parentWord =
      FactorTree.forestYield children := by
  cases children with
  | nil => simp at hcount
  | cons first tail =>
      cases tail with
      | nil => simp at hcount
      | cons second tail =>
          cases tail with
          | nil => simp at hcount
          | cons third rest =>
              exact
                (firstTwoForestAttachment C letter
                  (first :: second :: third :: rest)
                  hcount hforests left right payload hpayload
                  ).realizedParentWord_eq_forestYield

theorem firstTwoForestAttachment_slots
    (C : ControlMonoid M) (letter : α → M)
    (children : List (FactorTree α))
    (hcount : 3 ≤ children.length)
    (hforests :
      ∀ tree ∈ children, FactorTree.IsForest C letter tree)
    (left right payload : Word α)
    (hpayload : payload ≠ []) :
    let attachment :=
      (firstTwoForestAttachment C letter children hcount hforests
        left right payload hpayload).toForestWordAttachment
    attachment.toIntervalWordAttachment.leftSlot = 0 ∧
      attachment.toIntervalWordAttachment.rightSlot =
        (children.head (by
          intro hempty
          subst children
          simp at hcount)).yield.length := by
  cases children with
  | nil => simp at hcount
  | cons first tail =>
      cases tail with
      | nil => simp at hcount
      | cons second tail =>
          cases tail with
          | nil => simp at hcount
          | cons third rest =>
              simp [firstTwoForestAttachment,
                TwoForestAttachment.toForestWordAttachment,
                TwoForestAttachment.domains,
                ForestOccurrence.interval,
                forestChildInterval,
                ForestWordAttachment.toIntervalWordAttachment,
                IntervalWordAttachment.leftSlot,
                IntervalWordAttachment.rightSlot,
                IntervalWordAttachment.firstLocalStart,
                IntervalWordAttachment.secondLocalStart,
                ForestWordAttachment.parent,
                forestParentInterval,
                FactorTree.forestYield]
              omega

theorem firstTwoForestAttachment_middle_ne_nil
    (C : ControlMonoid M) (letter : α → M)
    (children : List (FactorTree α))
    (hcount : 3 ≤ children.length)
    (hforests :
      ∀ tree ∈ children, FactorTree.IsForest C letter tree)
    (left right payload : Word α)
    (hpayload : payload ≠ []) :
    let attachment :=
      (firstTwoForestAttachment C letter children hcount hforests
        left right payload hpayload).toForestWordAttachment
    attachment.toIntervalWordAttachment.orderedAttachment.middle ≠ [] := by
  dsimp only
  cases children with
  | nil => simp at hcount
  | cons first tail =>
      cases tail with
      | nil => simp at hcount
      | cons second tail =>
          cases tail with
          | nil => simp at hcount
          | cons third rest =>
              let attachment :=
                (firstTwoForestAttachment C letter
                  (first :: second :: third :: rest)
                  hcount hforests left right payload hpayload
                  ).toForestWordAttachment
              have hslots :=
                firstTwoForestAttachment_slots C letter
                  (first :: second :: third :: rest)
                  hcount hforests left right payload hpayload
              have hfirstForest :
                  FactorTree.IsForest C letter first :=
                hforests first (by simp)
              have hpositive :
                  0 < first.yield.length :=
                List.length_pos_iff.mpr
                  (FactorTree.isForest_wellFormed
                    C letter hfirstForest)
              intro hempty
              have hmiddle :=
                (attachment.toIntervalWordAttachment.orderedAttachment
                  ).middle_length
              rw [hempty] at hmiddle
              simp only [List.length_nil] at hmiddle
              dsimp only [attachment] at hslots hmiddle
              change
                0 =
                  ((firstTwoForestAttachment C letter
                    (first :: second :: third :: rest)
                    hcount hforests left right payload hpayload
                    ).toForestWordAttachment.toIntervalWordAttachment
                    ).rightSlot -
                  ((firstTwoForestAttachment C letter
                    (first :: second :: third :: rest)
                    hcount hforests left right payload hpayload
                    ).toForestWordAttachment.toIntervalWordAttachment
                    ).leftSlot at hmiddle
              rw [hslots.1, hslots.2] at hmiddle
              simp at hmiddle
              omega

theorem firstTwoForestAttachment_completeCompilerResponse
    [DecidableEq α]
    (C : ControlMonoid Wire) (letter : α → Wire)
    (forestChildren : List (FactorTree α))
    (hcount : 3 ≤ forestChildren.length)
    (hforests :
      ∀ tree ∈ forestChildren,
        FactorTree.IsForest C letter tree)
    (leftContext rightContext payload : Word α)
    (hpayload : payload ≠ [])
    (intervalChildren : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    let attachment :=
      (firstTwoForestAttachment C letter forestChildren hcount hforests
        leftContext rightContext payload hpayload
        ).toForestWordAttachment
    (∃ emitter :
        ContextualStructuralEmitter α Wire C letter predicates.length
          Ctl Cut Macro,
      emitter.singletonChain.finalState ≠ emitter.emitter.sourceState) ∨
      attachment.toIntervalWordAttachment.orderedAttachment.middle = [] ∨
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
  dsimp only
  exact
    (firstTwoForestAttachment C letter forestChildren hcount hforests
      leftContext rightContext payload hpayload
      ).toForestWordAttachment.completeCompilerResponse
        intervalChildren predicates wireOf strongWire C letter
        control cut macroData

end NSSE
