import NSSE.StoredTermLayoutBuild
import NSSE.StoredSubtermWeight

/-! Structural size envelopes, not executable size-computation counters. -/
namespace NSSE.StoredQuerySize
open StoredSubtypeTerm StoredTermQuery
variable {n : Nat}

def literalWeight : Literal n → Nat
  | .le a b | .eq a b => 1+weight a+weight b

def size (Q : Query n) := n+1+weight Q.left+weight Q.right+(Q.premises.map literalWeight).sum

theorem left (Q : Query n) : weight Q.left ≤ size Q := by unfold size; omega
theorem right (Q : Query n) : weight Q.right ≤ size Q := by unfold size; omega

theorem sum_member {α : Type*} (f : α → Nat) (xs : List α) (x : α) (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons,List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have h := ih hx; omega

theorem literal_bound (Q : Query n) (t : Literal n) (ht : t ∈ Q.premises) : literalWeight t ≤ size Q := by
  have h := sum_member literalWeight Q.premises t ht
  unfold size; omega

theorem pair_literal (t : Literal n) (p : Term n × Term n) (hp : p ∈ (inequalities t).1) :
    weight p.1 ≤ literalWeight t ∧ weight p.2 ≤ literalWeight t := by
  cases t <;> simp only [inequalities,List.mem_cons,List.not_mem_nil,or_false] at hp
  · subst p
    simp only [literalWeight]; constructor <;> omega
  · rcases hp with rfl | rfl <;> simp only [literalWeight] <;> constructor <;> omega

theorem pairs (Q : Query n) : ∀ p ∈ (expanded Q).1, weight p.1 ≤ size Q ∧ weight p.2 ≤ size Q := by
  intro p hp
  simp only [expanded,CountedListConstruction.flatMap_value,List.mem_flatMap] at hp
  obtain ⟨t,ht,hp⟩ := hp
  have h := pair_literal t p hp
  have hs := literal_bound Q t ht
  exact ⟨h.1.trans hs,h.2.trans hs⟩

theorem premises (Q : Query n) : Q.premises.length ≤ size Q := by
  have h (xs : List (Literal n)) : xs.length ≤ (xs.map literalWeight).sum := by
    induction xs with
    | nil => simp
    | cons t xs ih =>
      have ht : 1 ≤ literalWeight t := by cases t <;> simp only [literalWeight] <;> omega
      simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  have hh := h Q.premises
  unfold size; omega

theorem build_bound (Q : Query n) :
    (StoredTermLayoutBuild.build Q).2 ≤ StoredTermLayoutBuild.budget (size Q) (size Q) := by
  apply (StoredTermLayoutBuild.bound Q (size Q) (left Q) (right Q) (pairs Q)).trans
  unfold StoredTermLayoutBuild.budget
  have h := premises Q
  gcongr

theorem build_cubic (Q : Query n) :
    (StoredTermLayoutBuild.build Q).2 ≤ 16*(size Q)^3+18*(size Q)^2+24*size Q+9 := by
  calc
    _ ≤ StoredTermLayoutBuild.budget (size Q) (size Q) := build_bound Q
    _ = _ := by unfold StoredTermLayoutBuild.budget; ring

theorem pairCount (Q : Query n) : (StoredTermLayoutBuild.build Q).1.pairCount ≤ 2*size Q := by
  have h := StoredTermQuery.length_bound Q
  have hs := premises Q
  simp only [StoredTermLayoutBuild.build,StoredTermReference.length_value]
  omega

theorem termCount (Q : Query n) :
    (StoredTermLayoutBuild.build Q).1.termCount ≤ 2*size Q+4*(size Q)^2 := by
  have h := StoredLayoutTerms.length_bound Q.left Q.right (expanded Q).1 (size Q) (left Q) (right Q) (pairs Q)
  have hp := StoredTermQuery.length_bound Q
  have hs := premises Q
  have hh := Nat.mul_le_mul_right (2*size Q) (hp.trans (Nat.mul_le_mul_left 2 hs))
  simp only [StoredTermLayoutBuild.build,StoredTermReference.length_value]
  nlinarith
theorem generated_terms (Q : Query n) :
    ∀ t ∈ (StoredTermLayoutBuild.build Q).1.terms, weight t ≤ size Q := by
  intro t ht
  simp only [StoredTermLayoutBuild.build,StoredLayoutTerms.terms,
    CountedListConstruction.append_value,CountedListConstruction.flatMap_value,
    List.mem_append,List.mem_flatMap] at ht
  rcases ht with (hl | hr) | ⟨p,hp,ht⟩
  · exact (StoredSubtermWeight.bound Q.left t hl).trans (left Q)
  · exact (StoredSubtermWeight.bound Q.right t hr).trans (right Q)
  · have h := pairs Q p hp
    simp only [StoredLayoutTerms.pair,CountedListConstruction.append_value,List.mem_append] at ht
    rcases ht with hl | hr
    · exact (StoredSubtermWeight.bound p.1 t hl).trans h.1
    · exact (StoredSubtermWeight.bound p.2 t hr).trans h.2

end NSSE.StoredQuerySize
