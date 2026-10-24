import NSSE.IndexedRootQueries

/-!
# A length-minimal avoider cannot descend to a shorter avoider

Proper candidate-preserving contractions of a minimal avoider are covered,
not avoiders.  This rules out using shorter avoiders as provenance children
in the long-word compiler.
-/

namespace NSSE

namespace SOAInstance

theorem LengthMinimalAvoider.not_avoider_of_shorter
    {I : SOAInstance α} {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hshort : shorter.length < word.length) :
    ¬ I.Avoider shorter := by
  intro havoider
  have hminimum := hminimal.2 shorter havoider
  omega

theorem LengthMinimalAvoider.not_exists_shorter_avoider
    {I : SOAInstance α} {word : Word α}
    (hminimal : I.LengthMinimalAvoider word) :
    ¬ ∃ shorter : Word α,
        I.Avoider shorter ∧ shorter.length < word.length := by
  rintro ⟨shorter, havoider, hshort⟩
  exact hminimal.not_avoider_of_shorter hshort havoider

theorem LengthMinimalAvoider.shorter_candidate_iff_covered
    {I : SOAInstance α} {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length) :
    (¬ I.Avoider shorter) ∧ I.RootCov shorter := by
  exact ⟨hminimal.not_avoider_of_shorter hshort,
    covered_of_candidate_shorter hminimal hcandidate hshort⟩

theorem LengthMinimalAvoider.exists_indexedRootQuery_of_shorter_candidate
    {I : SOAInstance α} {word shorter : Word α}
    (hminimal : I.LengthMinimalAvoider word)
    (hcandidate : I.candidate shorter)
    (hshort : shorter.length < word.length) :
    ∃ index : Fin I.rows.length,
      I.IndexedRootQuery index shorter :=
  (I.rootCov_iff_exists_indexedRootQuery shorter).1
    (covered_of_candidate_shorter hminimal hcandidate hshort)

end SOAInstance

end NSSE
