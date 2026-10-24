import NSSE.MinimalAvoiderNoDescent
import NSSE.IndexedRootMaskSemantics

/-!
# Generalized replacement below a length-minimal avoider

For a shorter candidate, the abstract candidate trichotomy cannot return a
shorter avoider.  It therefore returns either a positive currently forbidden
query or a generalized representative satisfying the same forbidden mask.
-/

namespace NSSE

namespace SOAInstance.LengthMinimalAvoider

def IndexedMaskPredicate
    (I : SOAInstance α) (mask : List Bool) :
    Fin I.rows.length → Prop :=
  fun index =>
    maskBit mask
      (enumerationIndex I.indexedRootQueryEnumeration index) = true

theorem shorter_candidate_forbiddenQuery_or_generalized
    {I : SOAInstance α} {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (mask : List Bool) :
    (∃ index : Fin I.rows.length,
      IndexedMaskPredicate I mask index ∧
      I.IndexedRootQuery index shorter) ∨
    I.asProblem.Generalized I.IndexedRootQuery
      (IndexedMaskPredicate I mask) shorter := by
  rcases SOAProblem.candidate_trichotomy
      I.asProblem I.IndexedRootQuery
      (IndexedMaskPredicate I mask) hcandidate with
    havoider | hquery | hgeneralized
  · obtain ⟨found, hreduce, hfound⟩ := havoider
    have hfoundConcrete : I.Avoider found := hfound
    have hfoundShorter :
        found.length < word.length := by
      have hreduceShort :=
        I.asProblem.reduction_shorter hreduce
      omega
    exact False.elim
      (hminimal.not_avoider_of_shorter
        hfoundShorter hfoundConcrete)
  · exact Or.inl hquery
  · exact Or.inr hgeneralized

theorem shorter_candidate_generalized_of_indexedMaskForbids
    {I : SOAInstance α} {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length)
    (mask : List Bool)
    (hforbids : I.IndexedMaskForbids mask shorter) :
    I.asProblem.Generalized I.IndexedRootQuery
      (IndexedMaskPredicate I mask) shorter := by
  rcases hminimal.shorter_candidate_forbiddenQuery_or_generalized
      hcandidate hshort mask with hquery | hgeneralized
  · obtain ⟨index, hmarked, hpositive⟩ := hquery
    exact False.elim (hforbids index hmarked hpositive)
  · exact hgeneralized

theorem indexedMaskForbids_iff_forbids_maskPredicate
    (I : SOAInstance α) (mask : List Bool) (word : Word α) :
    I.IndexedMaskForbids mask word ↔
      SOAProblem.Forbids I.IndexedRootQuery
        (IndexedMaskPredicate I mask) word := by
  rfl

end SOAInstance.LengthMinimalAvoider

end NSSE
