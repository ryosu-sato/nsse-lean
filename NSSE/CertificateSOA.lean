import NSSE.ConcreteSOA

/-!
# Certificate normal form and SOA distillation

This combines the component normal form with the `(j,t)` occurrence
coordinates and formalizes the semantic content of Theorems 9.1 and 9.2.
Regularity/effective automaton construction is intentionally a separate
layer.
-/

namespace NSSE

universe u

def OccurrenceCertificateFree
    (E : CapExpression α) (w : Word α) : Prop :=
  routeFree E w ∧
  ∀ component ∈ E.caps,
    ¬PrefixRoute component w ∧
    ¬SplitRoute component w ∧
    ¬MarkedOccurrence component w

/-- Theorem 9.1 in literal `(j,t)` suffix-occurrence coordinates. -/
theorem uncovered_iff_occurrenceCertificateFree
    (E : CapExpression α)
    (hright :
      ∀ component ∈ E.caps,
        ∃ word, component.right word)
    (w : Word α) :
    E.Uncovered w ↔ OccurrenceCertificateFree E w := by
  rw [uncovered_iff_certificateUncovered_of_nonempty_right
    E hright w]
  unfold CertificateUncovered OccurrenceCertificateFree
  constructor
  · rintro ⟨hroute, hnormal⟩
    refine ⟨hroute, ?_⟩
    intro component hcomponent
    have hn := hnormal component hcomponent
    refine ⟨?_, ?_, ?_⟩
    · intro hprefix
      exact hn (Or.inl hprefix)
    · intro hsplit
      exact hn (Or.inr (Or.inl hsplit))
    · intro hmarked
      exact hn (Or.inr (Or.inr
        ((periodicWitness_iff_markedOccurrence
          component w).2 hmarked)))
  · rintro ⟨hroute, hfree⟩
    refine ⟨hroute, ?_⟩
    intro component hcomponent hnormal
    obtain ⟨hprefix, hsplit, hmarked⟩ :=
      hfree component hcomponent
    rcases hnormal with hp | hs | hw
    · exact hprefix hp
    · exact hsplit hs
    · exact hmarked
        ((periodicWitness_iff_markedOccurrence
          component w).1 hw)

/-- The candidate language obtained after removing every regular
non-occurrence certificate. -/
def certificateCandidate
    (E : CapExpression α) : Language α := fun w =>
  routeFree E w ∧
  ∀ component ∈ E.caps,
    ¬PrefixRoute component w ∧
    ¬SplitRoute component w

/-- The semantic SOA instance distilled from a cap expression. -/
def CapExpression.toSOAInstance
    (E : CapExpression α) : SOAInstance α where
  candidate := certificateCandidate E
  rows := E.caps

/-- Theorem 9.2: uncovered words are exactly avoiders of the distilled
suffix-occurrence instance. -/
theorem uncovered_iff_toSOA_avoider
    (E : CapExpression α)
    (hright :
      ∀ component ∈ E.caps,
        ∃ word, component.right word)
    (w : Word α) :
    E.Uncovered w ↔ E.toSOAInstance.Avoider w := by
  rw [uncovered_iff_occurrenceCertificateFree
    E hright w]
  change
    (routeFree E w ∧
      ∀ component ∈ E.caps,
        ¬PrefixRoute component w ∧
        ¬SplitRoute component w ∧
        ¬MarkedOccurrence component w) ↔
    ((routeFree E w ∧
      ∀ component ∈ E.caps,
        ¬PrefixRoute component w ∧
        ¬SplitRoute component w) ∧
      ¬∃ component ∈ E.caps,
        MarkedOccurrence component w)
  constructor
  · rintro ⟨hroute, hcomponents⟩
    refine ⟨⟨hroute, ?_⟩, ?_⟩
    · intro component hcomponent
      exact ⟨(hcomponents component hcomponent).1,
        (hcomponents component hcomponent).2.1⟩
    · rintro ⟨component, hcomponent, hmarked⟩
      exact (hcomponents component hcomponent).2.2 hmarked
  · rintro ⟨⟨hroute, hregular⟩, hoccurrence⟩
    refine ⟨hroute, ?_⟩
    intro component hcomponent
    refine ⟨(hregular component hcomponent).1,
      (hregular component hcomponent).2, ?_⟩
    intro hmarked
    exact hoccurrence ⟨component, hcomponent, hmarked⟩

/-- Nonuniversality is equivalent to existence of an SOA avoider. -/
theorem not_universal_iff_exists_toSOA_avoider
    (E : CapExpression α)
    (hright :
      ∀ component ∈ E.caps,
        ∃ word, component.right word) :
    ¬E.Universal ↔
      ∃ w, E.toSOAInstance.Avoider w := by
  rw [not_universal_iff_exists_uncovered]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (uncovered_iff_toSOA_avoider
      E hright w).1 hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (uncovered_iff_toSOA_avoider
      E hright w).2 hw⟩

end NSSE
