import NSSE.MinimalAvoiderNoDescent
import NSSE.GeneralizedStateMaskProgress
import NSSE.IndexedRootMaskSemantics

/-!
# Emitting covered contractions into indexed forbidden masks

A proper candidate contraction of a length-minimal avoider is covered by a
concrete indexed root query.  When the transition label emits that query
index, the canonical labelled child state has the corresponding forbidden
bit set.
-/

namespace NSSE

def MinimalAvoiderMaskInvariant
    (I : SOAInstance α) (word : Word α)
    (state :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length) : Prop :=
  I.LengthMinimalAvoider word ∧
    I.IndexedMaskForbids state.1.forbidden word

theorem MinimalAvoiderMaskInvariant.labelledChild
    (I : SOAInstance α) {word : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : Tag) :
    MinimalAvoiderMaskInvariant I word
      ⟨labelledChildState labels parent.1.tag
          parent.1.guarded parent.1.forbidden childTag,
        labelledChildState_valid labels parent.1.tag childTag
          parent.1.guarded parent.1.forbidden parent.2⟩ := by
  exact ⟨hminimal, hminimal.indexedMaskForbids _⟩

theorem exists_labelledChildState_marking_shorter_root
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : Tag)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag) :
    ∃ child :
        ValidGeneralizedState Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      child.1 =
          labelledChildState labels parent.1.tag
            parent.1.guarded parent.1.forbidden childTag ∧
      ∃ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter ∧
        maskBit child.1.forbidden
          (enumerationIndex I.indexedRootQueryEnumeration index) =
            true := by
  obtain ⟨index, hquery⟩ :=
    hminimal.exists_indexedRootQuery_of_shorter_candidate
      hcandidate hshort
  let childState :=
    labelledChildState labels parent.1.tag
      parent.1.guarded parent.1.forbidden childTag
  have hvalid :
      childState.Valid atomCount
        I.indexedRootQueryEnumeration.values.length :=
    labelledChildState_valid labels parent.1.tag childTag
      parent.1.guarded parent.1.forbidden parent.2
  refine ⟨⟨childState, hvalid⟩, rfl, index, hquery, ?_⟩
  exact maskBit_markMany_of_mem
    (labels.forbidden parent.1.tag childTag)
    parent.1.forbidden
    (enumerationIndex I.indexedRootQueryEnumeration index)
    (emits index hquery)
    (by
      have hlength := parent.2.2
      rw [hlength]
      exact enumerationIndex_lt I.indexedRootQueryEnumeration index)

theorem exists_labelledChildState_progress_of_unseen_shorter_root
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : Tag)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag)
    (unseen :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        maskBit parent.1.forbidden
          (enumerationIndex I.indexedRootQueryEnumeration index) =
            false) :
    ∃ child :
        ValidGeneralizedState Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      child.1 =
          labelledChildState labels parent.1.tag
            parent.1.guarded parent.1.forbidden childTag ∧
      remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length child.1 <
        remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length parent.1 := by
  obtain ⟨child, hchild, index, hquery, hmarked⟩ :=
    exists_labelledChildState_marking_shorter_root
      I hminimal hcandidate hshort labels parent childTag emits
  refine ⟨child, hchild, ?_⟩
  apply remainingCapacity_lt_of_forbidden_emission_false
    labels parent child
    (index := enumerationIndex I.indexedRootQueryEnumeration index)
  · rw [hchild]
    simp [allStateMasksFollow, labelledChildState,
      maskEqB_correct]
  · simpa [hchild, labelledChildState] using emits index hquery
  · rw [parent.2.2]
    exact enumerationIndex_lt I.indexedRootQueryEnumeration index
  · exact unseen index hquery

theorem marked_shorter_root_or_labelledChildState_progress
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : Tag)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag) :
    (∃ index : Fin I.rows.length,
      maskBit parent.1.forbidden
          (enumerationIndex I.indexedRootQueryEnumeration index) =
        true ∧
      I.IndexedRootQuery index shorter) ∨
    ∃ child :
        ValidGeneralizedState Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      MinimalAvoiderMaskInvariant I word child ∧
      child.1 =
          labelledChildState labels parent.1.tag
            parent.1.guarded parent.1.forbidden childTag ∧
      remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length child.1 <
        remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length parent.1 := by
  by_cases hmarked :
      ∃ index : Fin I.rows.length,
        maskBit parent.1.forbidden
            (enumerationIndex I.indexedRootQueryEnumeration index) =
          true ∧
        I.IndexedRootQuery index shorter
  · exact Or.inl hmarked
  · right
    obtain ⟨child, hchild, hprogress⟩ :=
      exists_labelledChildState_progress_of_unseen_shorter_root
        I hminimal hcandidate hshort labels parent childTag emits
        (by
          intro index hquery
          cases hbit :
              maskBit parent.1.forbidden
                (enumerationIndex
                  I.indexedRootQueryEnumeration index) with
          | false => rfl
          | true =>
              exact False.elim
                (hmarked ⟨index, hbit, hquery⟩))
    exact ⟨child,
      ⟨hminimal, hminimal.indexedMaskForbids _⟩,
      hchild, hprogress⟩

theorem indexedMaskForbids_contradicts_marked_positive_query
    (I : SOAInstance α)
    (mask : List Bool) (word : Word α)
    (hforbids : I.IndexedMaskForbids mask word)
    (index : Fin I.rows.length)
    (hmarked :
      maskBit mask
        (enumerationIndex I.indexedRootQueryEnumeration index) = true)
    (hquery : I.IndexedRootQuery index word) :
    False :=
  hforbids index hmarked hquery

theorem exists_labelledChildState_progress_of_shorter_masked_candidate
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : Tag)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag)
    (hforbids :
      I.IndexedMaskForbids parent.1.forbidden shorter) :
    ∃ child :
        ValidGeneralizedState Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      child.1 =
          labelledChildState labels parent.1.tag
            parent.1.guarded parent.1.forbidden childTag ∧
      remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length child.1 <
        remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length parent.1 := by
  apply exists_labelledChildState_progress_of_unseen_shorter_root
    I hminimal hcandidate hshort labels parent childTag emits
  intro index hquery
  cases hbit :
      maskBit parent.1.forbidden
        (enumerationIndex I.indexedRootQueryEnumeration index) with
  | false =>
      rfl
  | true =>
      exact False.elim
        (indexedMaskForbids_contradicts_marked_positive_query
          I parent.1.forbidden shorter hforbids index hbit hquery)

theorem exists_labelledChildState_progress_preserving_minimal_invariant
    (I : SOAInstance α)
    {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (labels : TransitionMaskLabels Tag)
    (parent :
      ValidGeneralizedState Tag atomCount
        I.indexedRootQueryEnumeration.values.length)
    (childTag : Tag)
    (emits :
      ∀ index : Fin I.rows.length,
        I.IndexedRootQuery index shorter →
        enumerationIndex I.indexedRootQueryEnumeration index ∈
          labels.forbidden parent.1.tag childTag)
    (hforbids :
      I.IndexedMaskForbids parent.1.forbidden shorter) :
    ∃ child :
        ValidGeneralizedState Tag atomCount
          I.indexedRootQueryEnumeration.values.length,
      MinimalAvoiderMaskInvariant I word child ∧
      child.1 =
          labelledChildState labels parent.1.tag
            parent.1.guarded parent.1.forbidden childTag ∧
      remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length child.1 <
        remainingMaskCapacity atomCount
          I.indexedRootQueryEnumeration.values.length parent.1 := by
  obtain ⟨child, hchild, hprogress⟩ :=
    exists_labelledChildState_progress_of_shorter_masked_candidate
      I hminimal hcandidate hshort labels parent childTag
      emits hforbids
  refine ⟨child, ?_, hchild, hprogress⟩
  exact ⟨hminimal, hminimal.indexedMaskForbids _⟩

end NSSE
