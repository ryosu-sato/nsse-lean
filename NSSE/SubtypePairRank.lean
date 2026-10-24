import NSSE.SubtypeCycleClashes

/-! # A bounded finite rank from absence of the ACTUAL C4

The rank is constructed inside a theorem from finite descendant sets.
It is proof data, not an oracle or an input to the finite-model program.
-/

namespace NSSE.SubtypePairRank

open SubtypeConstraints SubtypePathBounds SubtypeCycleClashes

variable {n d : Nat}

def Reach (φ : Constraints n d) (p q : Fin n × Fin n) : Prop :=
  ∃ word, word ≠ [] ∧ Support φ p.1 p.2 ∧
    LowerPath φ p.1 word q.1 ∧ UpperPath φ p.2 word q.2

theorem reach_trans (φ : Constraints n d) {p q r : Fin n × Fin n}
    (h : Reach φ p q) (k : Reach φ q r) : Reach φ p r := by
  obtain ⟨word,hw,hs,hl,hu⟩ := h
  obtain ⟨tail,_,_,kl,ku⟩ := k
  refine ⟨word ++ tail,?_,hs,lower_append φ hl kl,upper_append φ hu ku⟩
  intro he
  have hh := congrArg List.length he
  have hp := List.length_pos_iff.mpr hw
  simp only [List.length_append, List.length_nil] at hh
  omega

theorem reach_irrefl (φ : Constraints n d) (hc : ¬ CycleClash φ) (p : Fin n × Fin n) :
    ¬ Reach φ p p := by
  rintro ⟨word,hw,hs,hl,hu⟩
  exact hc ⟨p.1,p.2,word,hw,hs,hl,hu⟩

theorem one_reach (φ : Constraints n d) {a b c e : Fin n} {i : Fin d}
    (hs : Support φ a b) (hl : SupportedLower φ a i c) (hu : SupportedUpper φ b i e) :
    Reach φ (a,b) (c,e) :=
  ⟨[i],by simp,hs,.cons hl (.nil (.refl _)),.cons hu (.nil (.refl _))⟩

/-- A strict reachable-descendant count is below n*n. Its existence is
PROVED from noC4, not supplied to the public finite-model construction. -/
theorem exists_rank (φ : Constraints n d) (hc : ¬ CycleClash φ) :
    ∃ μ : (Fin n × Fin n) → Nat,
      (∀ p, μ p < n * n) ∧ (∀ p q, Reach φ p q → μ q < μ p) := by
  classical
  let descendants (p : Fin n × Fin n) : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun q => Reach φ p q)
  have hnot (p : Fin n × Fin n) : p ∉ descendants p := by
    intro hp
    exact reach_irrefl φ hc p (Finset.mem_filter.mp hp).2
  refine ⟨fun p => (descendants p).card,?_,?_⟩
  · intro p
    have hsub : descendants p ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _,?_⟩
      intro he
      apply hnot p
      rw [he]
      exact Finset.mem_univ _
    have hh := Finset.card_lt_card hsub
    simpa using hh
  · intro p q hpq
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,reach_trans φ hpq (Finset.mem_filter.mp hr).2⟩
    · intro he
      have hq : q ∈ descendants p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpq⟩
      rw [← he] at hq
      exact hnot q hq

end NSSE.SubtypePairRank
