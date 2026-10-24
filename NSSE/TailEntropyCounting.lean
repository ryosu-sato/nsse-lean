import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# The counting core of the Tail Entropy Theorem

This isolates the finite pigeonhole argument in `proofs_en.md`, Theorem
6.1. The word-geometric part must show that every covered completion is
one of `n` long-period codes or one of `n²` short-period codes.
-/

namespace NSSE

universe u

/-- If every covered member of a finite family is selected by either an
`n`-parameter code or an `n²`-parameter code, a family larger than
`n²+n` contains an uncovered member. -/
theorem tailEntropy_counting
    [DecidableEq β]
    (Covered : β → Prop)
    (completions : Finset β)
    (n : Nat)
    (longCode : Fin n → β)
    (shortCode : Fin n × Fin n → β)
    (hclassify :
      ∀ v ∈ completions, Covered v →
        (∃ endpoint, longCode endpoint = v) ∨
        (∃ anchorPeriod, shortCode anchorPeriod = v))
    (hmany : n * n + n < completions.card) :
    ∃ v ∈ completions, ¬Covered v := by
  classical
  let longValues : Finset β := Finset.univ.image longCode
  let shortValues : Finset β := Finset.univ.image shortCode
  have hlongCard : longValues.card ≤ n := by
    dsimp [longValues]
    calc
      (Finset.univ.image longCode).card ≤ Finset.univ.card :=
        Finset.card_image_le
      _ = n := by simp
  have hshortCard : shortValues.card ≤ n * n := by
    dsimp [shortValues]
    calc
      (Finset.univ.image shortCode).card ≤ Finset.univ.card :=
        Finset.card_image_le
      _ = n * n := by simp
  by_contra hnone
  push_neg at hnone
  have hsubset :
      completions ⊆ longValues ∪ shortValues := by
    intro v hv
    rcases hclassify v hv (hnone v hv) with
      ⟨endpoint, rfl⟩ | ⟨anchorPeriod, rfl⟩
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨endpoint, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr
          ⟨anchorPeriod, Finset.mem_univ _, rfl⟩)
  have hcompletionCard :
      completions.card ≤ (longValues ∪ shortValues).card :=
    Finset.card_le_card hsubset
  have hunionCard :
      (longValues ∪ shortValues).card ≤ n * n + n := by
    calc
      (longValues ∪ shortValues).card ≤
          longValues.card + shortValues.card :=
        Finset.card_union_le longValues shortValues
      _ ≤ n + n * n := Nat.add_le_add hlongCard hshortCard
      _ = n * n + n := Nat.add_comm _ _
  omega

/-- Relation-based form: it is enough that every covered object belongs
to a right-unique family indexed by either `Fin n` or `Fin n × Fin n`. -/
theorem tailEntropy_counting_relations
    [DecidableEq β] [Inhabited β]
    (Covered : β → Prop)
    (completions : Finset β)
    (n : Nat)
    (Long : Fin n → β → Prop)
    (Short : Fin n × Fin n → β → Prop)
    (hlongUnique :
      ∀ i x y, Long i x → Long i y → x = y)
    (hshortUnique :
      ∀ i x y, Short i x → Short i y → x = y)
    (hclassify :
      ∀ v ∈ completions, Covered v →
        (∃ i, Long i v) ∨ (∃ i, Short i v))
    (hmany : n * n + n < completions.card) :
    ∃ v ∈ completions, ¬Covered v := by
  classical
  let longCode : Fin n → β := fun i =>
    if h : ∃ v, Long i v then Classical.choose h else default
  let shortCode : Fin n × Fin n → β := fun i =>
    if h : ∃ v, Short i v then Classical.choose h else default
  apply tailEntropy_counting Covered completions n
    longCode shortCode
  · intro v hv hcovered
    rcases hclassify v hv hcovered with
      ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      refine ⟨i, ?_⟩
      dsimp [longCode]
      rw [dif_pos ⟨v, hi⟩]
      exact hlongUnique i _ v
        (Classical.choose_spec (show ∃ x, Long i x from ⟨v, hi⟩))
        hi
    · right
      refine ⟨i, ?_⟩
      dsimp [shortCode]
      rw [dif_pos ⟨v, hi⟩]
      exact hshortUnique i _ v
        (Classical.choose_spec (show ∃ x, Short i x from ⟨v, hi⟩))
        hi
  · exact hmany

end NSSE
