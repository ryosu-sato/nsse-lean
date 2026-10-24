import NSSE.OccurrenceLoopProvenance
import NSSE.AutomataSOA

/-!
# Extracting occurrence-loop provenance from a forest contraction

At a length-minimal avoider, deleting an admissible idempotent child makes
the shortened word root-covered.  The covering row supplies an actual
marked occurrence, which is turned into a forward structural-loop
certificate carrying the separately computed normalized loop summary.
-/

namespace NSSE

universe u vc

def forwardOccurrenceLoop
    (row : CapComponent α) (word : Word α)
    (summary : LoopSummary Wire)
    (occurrence : MarkedOccurrence row word) :
    OrientedOccurrenceLoop α Wire where
  theta := id
  orientation := .forward
  row := row
  word := word
  sourceWire := summary.sourceWire
  targetWire := summary.targetWire
  displacement := summary.displacement
  occurrence := by
    simpa [Word.orient] using occurrence

@[simp] theorem forwardOccurrenceLoop_summary
    (row : CapComponent α) (word : Word α)
    (summary : LoopSummary Wire)
    (occurrence : MarkedOccurrence row word) :
    (forwardOccurrenceLoop row word summary occurrence).summary =
      summary := by
  rfl

theorem idempotent_child_has_occurrenceLoop
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
          (before ++ deleted :: after) ++ right))
    (summary : LoopSummary Wire) :
    ∃ row,
      row ∈ I.toSOA.rows ∧
      ∃ cycle : OrientedOccurrenceLoop α Wire,
        cycle.row = row ∧
        cycle.word =
          left ++ FactorTree.forestYield (before ++ after) ++ right ∧
        cycle.summary = summary := by
  have hroot :=
    AutomataSOAInstance.idempotent_child_rootCov_of_minimal
      I he hall hretained hdeleted left right hminimal
  obtain ⟨row, hrow, hoccurrence⟩ := hroot
  let cycle :=
    forwardOccurrenceLoop row
      (left ++ FactorTree.forestYield (before ++ after) ++ right)
      summary hoccurrence
  exact ⟨row, hrow, cycle, rfl, rfl, rfl⟩

theorem idempotent_child_identity_or_VBRP
    [DecidableEq Wire]
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
          (before ++ deleted :: after) ++ right))
    (summary : LoopSummary Wire) :
    IdentityLoop summary ∨
      ∃ row,
        row ∈ I.toSOA.rows ∧
        PeriodicWitness row
          (left ++ FactorTree.forestYield (before ++ after) ++ right) ∧
        HornDerives
          (loopCompilerTerminalHornFamily summary).compiler
          (loopCompilerTerminalHornFamily summary).root := by
  by_cases hidentity : IdentityLoop summary
  · exact Or.inl hidentity
  · apply Or.inr
    have hroot :=
      AutomataSOAInstance.idempotent_child_rootCov_of_minimal
        I he hall hretained hdeleted left right hminimal
    obtain ⟨row, hrow, hoccurrence⟩ := hroot
    have hperiodic :
        PeriodicWitness row
          (left ++ FactorTree.forestYield (before ++ after) ++ right) :=
      (periodicWitness_iff_markedOccurrence row _).2 hoccurrence
    exact ⟨row, hrow, hperiodic,
      (loopCompilerTerminalHornFamily_derives_iff summary).2
        hidentity⟩

end NSSE
