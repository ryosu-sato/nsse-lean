import NSSE.IndexedRootQueries
import NSSE.CanonicalForbiddenTransitionLabels

/-!
# Semantics of the canonical forbidden-query mask

A true bit asserts absence of the corresponding indexed root query for one
fixed representative word.  When every row index is true, root coverage is
impossible, so candidate membership yields an actual avoider.
-/

namespace NSSE

universe u

def SOAInstance.IndexedMaskForbids
    (I : SOAInstance α) (mask : List Bool)
    (word : Word α) : Prop :=
  ∀ index : Fin I.rows.length,
    maskBit mask
        (enumerationIndex I.indexedRootQueryEnumeration index) = true →
      ¬ I.IndexedRootQuery index word

theorem SOAInstance.Avoider.indexedMaskForbids
    {I : SOAInstance α} {word : Word α}
    (havoider : I.Avoider word)
    (mask : List Bool) :
    I.IndexedMaskForbids mask word := by
  intro index _hmarked hquery
  apply havoider.2
  exact (I.rootCov_iff_exists_indexedRootQuery word).2
    ⟨index, hquery⟩

theorem SOAInstance.LengthMinimalAvoider.indexedMaskForbids
    {I : SOAInstance α} {word : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (mask : List Bool) :
    I.IndexedMaskForbids mask word :=
  hminimal.1.indexedMaskForbids mask

theorem SOAInstance.not_rootCov_of_fullIndexedMask
    (I : SOAInstance α) (mask : List Bool)
    (word : Word α)
    (hfull :
      ∀ index : Fin I.rows.length,
        maskBit mask
          (enumerationIndex I.indexedRootQueryEnumeration index) = true)
    (hforbids : I.IndexedMaskForbids mask word) :
    ¬ I.RootCov word := by
  rw [I.rootCov_iff_exists_indexedRootQuery]
  rintro ⟨index, hquery⟩
  exact hforbids index (hfull index) hquery

theorem SOAInstance.avoider_of_fullIndexedMask
    (I : SOAInstance α) (mask : List Bool)
    (word : Word α)
    (hcandidate : I.candidate word)
    (hfull :
      ∀ index : Fin I.rows.length,
        maskBit mask
          (enumerationIndex I.indexedRootQueryEnumeration index) = true)
    (hforbids : I.IndexedMaskForbids mask word) :
    I.Avoider word :=
  ⟨hcandidate,
    I.not_rootCov_of_fullIndexedMask mask word hfull hforbids⟩

theorem SOAInstance.critical_of_fullIndexedMask
    (I : SOAInstance α) (mask : List Bool)
    (word : Word α)
    (hcandidate : I.candidate word)
    (hallDel : I.AllDel word)
    (hfull :
      ∀ index : Fin I.rows.length,
        maskBit mask
          (enumerationIndex I.indexedRootQueryEnumeration index) = true)
    (hforbids : I.IndexedMaskForbids mask word) :
    I.Critical word :=
  ⟨hcandidate, hallDel,
    I.not_rootCov_of_fullIndexedMask mask word hfull hforbids⟩

theorem SOAInstance.avoider_of_allCanonicalMaskTerminal
    (I : SOAInstance α)
    (guardedRequired : Tag → List Nat)
    (atomCount : Nat)
    (state :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (word : Word α)
    (hterminal :
      requiredMasksTerminal
          (allCanonicalForbiddenRequirement
            I.indexedRootQueryEnumeration guardedRequired)
          atomCount I.indexedRootQueryEnumeration.values.length
          state = true)
    (hcandidate : I.candidate word)
    (hforbids :
      I.IndexedMaskForbids state.1.forbidden word) :
    I.Avoider word := by
  apply I.avoider_of_fullIndexedMask
    state.1.forbidden word hcandidate
  · intro index
    have hall :=
      (allCanonicalForbiddenRequirement_correct
        I.indexedRootQueryEnumeration guardedRequired
        atomCount state).1 hterminal
    exact hall.2 index
  · exact hforbids

end NSSE
