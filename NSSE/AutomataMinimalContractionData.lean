import NSSE.AutomataSOA
import NSSE.IndexedRootQueries

/-!
# Candidate-aligned contraction data

Completeness must build its factor forest in the transformation monoid of
the candidate automaton.  Only then does deleting an idempotent child
preserve candidate membership.
-/

namespace NSSE

theorem AutomataSOAInstance.idempotent_child_contractionData
    (I : AutomataSOAInstance α QC QL QR)
    {before after : List (FactorTree α)}
    {deleted : FactorTree α} {e : QC → QC}
    (he : (transformationMonoid QC).Idempotent e)
    (hall :
      ∀ tree ∈ before ++ deleted :: after,
        FactorTree.control (transformationMonoid QC)
          I.candidate.letterTransform tree = e)
    (hretained : before ++ after ≠ [])
    (hdeleted : deleted.WellFormed)
    (left right : Word α)
    (hminimal :
      I.toSOA.LengthMinimalAvoider
        (left ++ FactorTree.forestYield
          (before ++ deleted :: after) ++ right)) :
    let original :=
      left ++ FactorTree.forestYield
        (before ++ deleted :: after) ++ right
    let shorter :=
      left ++ FactorTree.forestYield (before ++ after) ++ right
    I.toSOA.DeletesTo shorter original ∧
      I.toSOA.candidate shorter ∧
      shorter.length < original.length ∧
      ∃ index : Fin I.toSOA.rows.length,
        I.toSOA.IndexedRootQuery index shorter := by
  dsimp only
  let shorter :=
    left ++ FactorTree.forestYield (before ++ after) ++ right
  let original :=
    left ++ FactorTree.forestYield
      (before ++ deleted :: after) ++ right
  have hdelete : I.toSOA.DeletesTo shorter original :=
    I.idempotent_child_deletesTo
      he hall hretained hdeleted left right hminimal.1.1
  have hcandidate : I.toSOA.candidate shorter :=
    SOAInstance.deletesTo_candidate hdelete
  have hshort : shorter.length < original.length :=
    SOAInstance.deletesTo_shorter hdelete
  have hcovered : I.toSOA.RootCov shorter :=
    SOAInstance.covered_of_candidate_shorter
      hminimal hcandidate hshort
  exact ⟨hdelete, hcandidate, hshort,
    (I.toSOA.rootCov_iff_exists_indexedRootQuery shorter).1 hcovered⟩

end NSSE
