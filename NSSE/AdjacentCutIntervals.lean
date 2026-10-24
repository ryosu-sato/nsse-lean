import NSSE.RamseyanTopIntervalForest
import NSSE.IdempotentBlockForest

/-!
# Word intervals induced by adjacent cuts

An ordered list of cuts determines the list of intervals between consecutive
cuts.  These intervals concatenate to the interval from the first cut to the
last, and properties proved for every adjacent pair transfer to every block.
-/

namespace NSSE

universe u

namespace WordCut

def adjacentIntervals
    (word : Word α) : List (WordCut word) → List (Word α)
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      interval word first second ::
        adjacentIntervals word (second :: rest)

theorem adjacentIntervals_ne_nil
    (word : Word α) (first second : WordCut word)
    (rest : List (WordCut word)) :
    adjacentIntervals word
      (first :: second :: rest) ≠ [] := by
  simp [adjacentIntervals]

theorem property_of_mem_adjacentIntervals
    (word : Word α)
    (cuts : List (WordCut word))
    (P : Word α → Prop)
    (hadjacent :
      ∀ before after : List (WordCut word),
        ∀ left right : WordCut word,
        cuts = before ++ left :: right :: after →
        P (interval word left right)) :
    ∀ block ∈ adjacentIntervals word cuts, P block := by
  induction cuts with
  | nil =>
      simp [adjacentIntervals]
  | cons first tail ih =>
      cases tail with
      | nil =>
          simp [adjacentIntervals]
      | cons second rest =>
          intro block hblock
          simp only [adjacentIntervals, List.mem_cons] at hblock
          rcases hblock with rfl | htail
          · exact hadjacent [] rest first second (by simp)
          · apply ih
            · intro before after left right hdecomp
              apply hadjacent (first :: before) after
                left right
              simp only [List.cons_append]
              rw [hdecomp]
            · exact htail

theorem adjacentIntervals_flatten
    (word : Word α)
    (first second : WordCut word)
    (rest : List (WordCut word))
    (hordered :
      (first :: second :: rest).Pairwise
        (fun left right => left.1 < right.1)) :
    (adjacentIntervals word
      (first :: second :: rest)).flatten =
      interval word first
        ((second :: rest).getLast (by simp)) := by
  induction rest generalizing first second with
  | nil =>
      simp [adjacentIntervals, List.getLast_singleton]
  | cons third tail ih =>
      have htailOrdered :
          (second :: third :: tail).Pairwise
            (fun left right => left.1 < right.1) := by
        rw [List.pairwise_cons] at hordered
        exact hordered.2
      have hfirstSecond :
          first.1 ≤ second.1 := by
        rw [List.pairwise_cons] at hordered
        exact Nat.le_of_lt
          (hordered.1 second (by simp))
      have hsecondLast :
          second.1 ≤
            ((third :: tail).getLast (by simp)).1 := by
        rw [List.pairwise_cons] at htailOrdered
        exact Nat.le_of_lt
          (htailOrdered.1
            ((third :: tail).getLast (by simp))
            (List.getLast_mem (by simp)))
      change
        interval word first second ++
            (adjacentIntervals word
              (second :: third :: tail)).flatten =
          interval word first
            ((second :: third :: tail).getLast (by simp))
      rw [ih second third htailOrdered]
      have hlast :
          (second :: third :: tail).getLast (by simp) =
            (third :: tail).getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hlast]
      exact WordCut.interval_append
        word first second
        ((third :: tail).getLast (by simp))
        hfirstSecond hsecondLast

end WordCut

namespace RamseyanSplit

noncomputable def topSpanForest
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (first second : WordCut word)
    (rest : List (WordCut word))
    (hcuts :
      split.topCuts = first :: second :: rest)
    (lowerForest :
      ∀ {lowerWord : Word α},
        RamseyanSplit C letter lowerWord height →
        lowerWord ≠ [] →
        FactorTree.HeightBoundedForest
          C letter lowerWord bound) :
    FactorTree.HeightBoundedForest C letter
      (WordCut.interval word first
        ((second :: rest).getLast (by simp)))
      (bound + 3) := by
  let cuts := first :: second :: rest
  let blocks := WordCut.adjacentIntervals word cuts
  have hordered :
      cuts.Pairwise
        (fun left right => left.1 < right.1) := by
    change
      (first :: second :: rest).Pairwise
        (fun left right => left.1 < right.1)
    rw [← hcuts]
    exact split.topCuts_pairwise_lt
  have hblocks : blocks ≠ [] :=
    WordCut.adjacentIntervals_ne_nil
      word first second rest
  have replacementExists :
      ∀ block ∈ blocks,
        Nonempty
          (FactorTree.HeightBoundedForest
            C letter block (bound + 2)) := by
    apply WordCut.property_of_mem_adjacentIntervals
      word cuts
      (fun block =>
        Nonempty
          (FactorTree.HeightBoundedForest
            C letter block (bound + 2)))
    intro before after left right hdecomp
    have htop :=
      split.topNeighbors_of_adjacent_topCuts
        before after left right
        (hcuts.trans hdecomp)
    exact ⟨split.topIntervalForest_of_lower
      htop lowerForest⟩
  let replacement :
      ∀ block ∈ blocks,
        FactorTree.HeightBoundedForest
          C letter block (bound + 2) :=
    fun block hblock =>
      Classical.choice
        (replacementExists block hblock)
  let value :=
    split.idempotentAt ⟨height, by omega⟩
  have hvalue : C.Idempotent value :=
    split.idempotent ⟨height, by omega⟩
  have hcontrol :
      ∀ block ∈ blocks,
        C.eval letter block = value := by
    apply WordCut.property_of_mem_adjacentIntervals
      word cuts
      (fun block => C.eval letter block = value)
    intro before after left right hdecomp
    exact split.adjacent_topCuts_control
      before after left right (hcuts.trans hdecomp)
  let assembled :=
    FactorTree.HeightBoundedForest.nonemptyIdempotentBlocks
      blocks hblocks replacement value hvalue hcontrol
  apply assembled.rewriteWord
    (WordCut.interval word first
      ((second :: rest).getLast (by simp)))
  exact WordCut.adjacentIntervals_flatten
    word first second rest hordered

end RamseyanSplit

end NSSE
