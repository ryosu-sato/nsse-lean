import NSSE.AttachmentStrongEmitter

/-!
# Complete compiler response for a word-bearing attachment

Side routing emits nonstrong.  At a local node, the insertion square is
either periodic or mismatching.  A nonempty periodic middle emits strong;
an empty middle is the genuine trivial case.
-/

namespace NSSE

universe u

theorem OrderedInsertionAttachment.slots_eq_of_middle_nil
    (attachment : OrderedInsertionAttachment α)
    (hmiddle : attachment.middle = []) :
    attachment.leftSlot = attachment.rightSlot := by
  have hlength := attachment.middle_length
  rw [hmiddle] at hlength
  simp only [List.length_nil] at hlength
  have hle := attachment.left_le_right
  omega

theorem OrderedInsertionAttachment.insertions_eq_of_middle_nil
    (attachment : OrderedInsertionAttachment α)
    (hmiddle : attachment.middle = []) :
    Word.insertAt attachment.base attachment.payload
        attachment.leftSlot =
      Word.insertAt attachment.base attachment.payload
        attachment.rightSlot := by
  rw [attachment.slots_eq_of_middle_nil hmiddle]

theorem IntervalWordAttachment.RoutingOutcome.completeCompilerResponse
    [DecidableEq α]
    {attachment : IntervalWordAttachment α}
    {children : List NatInterval}
    (outcome : attachment.RoutingOutcome children)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    (∃ emitter :
        ContextualStructuralEmitter α Wire C letter predicates.length
          Ctl Cut Macro,
      emitter.singletonChain.finalState ≠ emitter.emitter.sourceState) ∨
      attachment.orderedAttachment.middle = [] ∨
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
      let emitter :=
        attachment.nonstrongEmitter
          (predicateCount := predicates.length)
          delegation wireOf C letter control cut macroData
      apply Or.inl
      refine ⟨emitter, ?_⟩
      exact emitter.singletonChain_endpoint_ne_of_nonidentity
        (attachment.nonstrongEmitter_nonidentity
          (predicateCount := predicates.length)
          delegation wireOf C letter control cut macroData)
  | «local» _ ordered ordered_eq =>
      subst ordered
      rcases attachment.periodic_or_mismatchHorn with
        hperiodic | hmismatch
      · obtain ⟨root, m, n, hprimitive, hm, hpayload, hmiddle⟩ :=
          hperiodic
        by_cases hmiddleNonempty :
            attachment.orderedAttachment.middle = []
        · exact Or.inr (Or.inl hmiddleNonempty)
        · let certificate :
              PeriodicAttachmentCertificate attachment :=
            { root := root
              payloadExponent := m
              middleExponent := n
              primitive := hprimitive
              payloadExponent_positive := hm
              payload_power := hpayload
              middle_power := hmiddle
              middle_nonempty := hmiddleNonempty }
          obtain ⟨transition, hwords, emitter, hemits, hlca,
              hendpoint⟩ :=
            certificate.exists_endpointChangingStrongChain_ofArithmeticPredicates
              predicates strongWire C letter control cut macroData
          exact Or.inl ⟨emitter, hendpoint⟩
      · exact Or.inr (Or.inr hmismatch)

theorem ForestWordAttachment.completeCompilerResponse
    [DecidableEq α]
    (attachment : ForestWordAttachment α)
    (children : List NatInterval)
    (predicates : List UnaryArithmeticPredicate)
    (wireOf : NatInterval → Wire)
    (strongWire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
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
          attachment.payload).root :=
  (attachment.toIntervalWordAttachment.route children
    ).completeCompilerResponse
      predicates wireOf strongWire C letter control cut macroData

end NSSE
