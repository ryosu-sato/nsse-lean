import NSSE.AttachmentNonstrongEmitter
import NSSE.ExecutableEuclideanClassifier

/-!
# Emitting a strong geometry from the periodic attachment branch

The local periodic response gives two common-root powers.  When the
middle word is nonempty, they form a nonempty commuting Euclidean pair.
A supplied positive classifier then produces the checked bulk strong
transition and its contextual emitter.
-/

namespace NSSE

universe u

def EuclideanWordState.ofCommutingPair
    (first second : Word α)
    (hfirst : first ≠ []) (hsecond : second ≠ [])
    (hcommute : first ++ second = second ++ first) :
    EuclideanWordState α :=
  if hle : first.length ≤ second.length then
    { shorter := first
      longer := second
      shorter_nonempty := hfirst
      longer_nonempty := hsecond
      length_le := hle
      commute := hcommute }
  else
    { shorter := second
      longer := first
      shorter_nonempty := hsecond
      longer_nonempty := hfirst
      length_le := by omega
      commute := hcommute.symm }

structure PeriodicAttachmentCertificate
    (attachment : IntervalWordAttachment α) where
  root : Word α
  payloadExponent : Nat
  middleExponent : Nat
  primitive : root.IsPrimitive
  payloadExponent_positive : 0 < payloadExponent
  payload_power :
    attachment.payload = Word.power root payloadExponent
  middle_power :
    attachment.orderedAttachment.middle =
      Word.power root middleExponent
  middle_nonempty : attachment.orderedAttachment.middle ≠ []

namespace PeriodicAttachmentCertificate

variable {α : Type u}
  {attachment : IntervalWordAttachment α}

def words
    (certificate : PeriodicAttachmentCertificate attachment) :
    EuclideanWordState α :=
  EuclideanWordState.ofCommutingPair
    attachment.payload attachment.orderedAttachment.middle
    attachment.payload_nonempty certificate.middle_nonempty
    ((Word.commute_iff_common_power
      attachment.payload attachment.orderedAttachment.middle).2
      ⟨certificate.root, certificate.payloadExponent,
        certificate.middleExponent,
        certificate.payload_power, certificate.middle_power⟩)

theorem exists_contextualStrongEmitter
    {Wire : Type u}
    (certificate : PeriodicAttachmentCertificate attachment)
    (classifier : PositiveEuclideanClassifier predicateCount)
    (wire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ transition : BulkStrongTransition α Wire predicateCount,
      transition.words = certificate.words ∧
      let emitter :
          ContextualStructuralEmitter α Wire C letter predicateCount
            Ctl Cut Macro :=
        { emitter := .strong transition.profiled
          context :=
            { control := control
              cut := cut
              lca := attachment.parent
              macroData := macroData } }
      ¬ IdentityLoop
        (StructuralLoopStep.oneStepExecution
          emitter.emitter.sourceState emitter.emitter.emittedStep
          ).summary := by
  let bulk := Classical.choice certificate.words.exists_bulkWitness
  obtain ⟨profile, hprofile⟩ :=
    classifier.positive_complete
      bulk.quotient bulk.quotient_positive
  let transition : BulkStrongTransition α Wire predicateCount :=
    { words := certificate.words
      bulk := bulk
      classifier := classifier.toEuclideanClassifier
      profile := profile
      classified_quotient := hprofile
      wire := wire }
  refine ⟨transition, rfl, ?_⟩
  exact transition.profiled.emitted_nonidentity_of_positive
    transition.bulk.quotient_positive

theorem exists_endpointChangingStrongChain
    {Wire : Type u}
    (certificate : PeriodicAttachmentCertificate attachment)
    (classifier : PositiveEuclideanClassifier predicateCount)
    (wire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ transition : BulkStrongTransition α Wire predicateCount,
      transition.words = certificate.words ∧
      ∃ emitter :
          ContextualStructuralEmitter α Wire C letter predicateCount
            Ctl Cut Macro,
        emitter.emitter = .strong transition.profiled ∧
        emitter.context.lca = attachment.parent ∧
        emitter.singletonChain.finalState ≠
          emitter.emitter.sourceState := by
  obtain ⟨transition, hwords, hnonidentity⟩ :=
    certificate.exists_contextualStrongEmitter
      classifier wire C letter control cut macroData
  let emitter :
      ContextualStructuralEmitter α Wire C letter predicateCount
        Ctl Cut Macro :=
    { emitter := .strong transition.profiled
      context :=
        { control := control
          cut := cut
          lca := attachment.parent
          macroData := macroData } }
  refine ⟨transition, hwords, emitter, rfl, rfl, ?_⟩
  exact emitter.singletonChain_endpoint_ne_of_nonidentity hnonidentity

theorem exists_endpointChangingStrongChain_ofPredicates
    {Wire : Type u}
    (certificate : PeriodicAttachmentCertificate attachment)
    (predicates : List (Nat → Bool))
    (wire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ transition :
        BulkStrongTransition α Wire predicates.length,
      transition.words = certificate.words ∧
      ∃ emitter :
          ContextualStructuralEmitter α Wire C letter predicates.length
            Ctl Cut Macro,
        emitter.emitter = .strong transition.profiled ∧
        emitter.context.lca = attachment.parent ∧
        emitter.singletonChain.finalState ≠
          emitter.emitter.sourceState :=
  certificate.exists_endpointChangingStrongChain
    (executablePositiveEuclideanClassifier predicates)
    wire C letter control cut macroData

theorem exists_endpointChangingStrongChain_ofArithmeticPredicates
    {Wire : Type u}
    (certificate : PeriodicAttachmentCertificate attachment)
    (predicates : List UnaryArithmeticPredicate)
    (wire : Wire)
    (C : ControlMonoid Wire) (letter : α → Wire)
    (control : Ctl) (cut : Cut) (macroData : Macro) :
    ∃ transition :
        BulkStrongTransition α Wire predicates.length,
      transition.words = certificate.words ∧
      ∃ emitter :
          ContextualStructuralEmitter α Wire C letter predicates.length
            Ctl Cut Macro,
        emitter.emitter = .strong transition.profiled ∧
        emitter.context.lca = attachment.parent ∧
        emitter.singletonChain.finalState ≠
          emitter.emitter.sourceState := by
  exact certificate.exists_endpointChangingStrongChain
    (arithmeticPositiveEuclideanClassifier predicates)
    wire C letter control cut macroData

end PeriodicAttachmentCertificate

end NSSE
