import NSSE.StoredQuerySize

namespace NSSE.StoredQueryWellFormed
open StoredSubtypeTerm StoredTermQuery
variable {n d : Nat}

theorem subterms (t : Term n) : WellFormed d t → ∀ u ∈ (StoredSubterms.subterms t).1, WellFormed d u := by
  apply StoredSubterms.subterms.induct
    (motive1 := fun t => WellFormed d t → ∀ u ∈ (StoredSubterms.subterms t).1, WellFormed d u)
    (motive2 := fun ts => (∀ t ∈ ts, WellFormed d t) → ∀ u ∈ (StoredSubterms.forest ts).1, WellFormed d u)
  · intro x h u hu; simp only [StoredSubterms.subterms,List.mem_singleton] at hu; subst u; exact h
  · intro h u hu; simp only [StoredSubterms.subterms,List.mem_singleton] at hu; subst u; exact h
  · intro h u hu; simp only [StoredSubterms.subterms,List.mem_singleton] at hu; subst u; exact h
  · intro cs ih h u hu
    simp only [StoredSubterms.subterms,List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact h
    · simp only [WellFormed] at h
      exact ih h.2 u hu
  · intro h u hu; simp [StoredSubterms.forest] at hu
  · intro t ts ha hb h u hu
    simp only [StoredSubterms.forest,CountedListConstruction.append_value,List.mem_append] at hu
    rcases hu with hu | hu
    · exact ha (h t (by simp)) u hu
    · exact hb (fun v hv => h v (by simp [hv])) u hu

def literal (d : Nat) : Literal n → Prop
  | .le a b | .eq a b => WellFormed d a ∧ WellFormed d b

def query (d : Nat) (Q : Query n) : Prop :=
  WellFormed d Q.left ∧ WellFormed d Q.right ∧ ∀ t ∈ Q.premises, literal d t

theorem pairs (Q : Query n) (h : query d Q) :
    ∀ p ∈ (expanded Q).1, WellFormed d p.1 ∧ WellFormed d p.2 := by
  intro p hp
  simp only [expanded,CountedListConstruction.flatMap_value,List.mem_flatMap] at hp
  obtain ⟨t,ht,hp⟩ := hp
  have h := h.2.2 t ht
  cases t <;> simp only [inequalities,List.mem_cons,List.not_mem_nil,or_false] at hp
  · subst p; exact h
  · rcases hp with rfl | rfl
    · exact h
    · exact ⟨h.2,h.1⟩

theorem generated (Q : Query n) (h : query d Q) :
    ∀ t ∈ (StoredTermLayoutBuild.build Q).1.terms, WellFormed d t := by
  intro t ht
  simp only [StoredTermLayoutBuild.build,StoredLayoutTerms.terms,
    CountedListConstruction.append_value,CountedListConstruction.flatMap_value,
    List.mem_append,List.mem_flatMap] at ht
  rcases ht with (hl | hr) | ⟨p,hp,ht⟩
  · exact subterms Q.left h.1 t hl
  · exact subterms Q.right h.2.1 t hr
  · have h := pairs Q h p hp
    simp only [StoredLayoutTerms.pair,CountedListConstruction.append_value,List.mem_append] at ht
    rcases ht with hl | hr
    · exact subterms p.1 h.1 t hl
    · exact subterms p.2 h.2 t hr

theorem packed (Q : SubtypeTerms.Query n d) : query d (packQuery Q) := by
  refine ⟨pack_wellFormed Q.left,pack_wellFormed Q.right,?_⟩
  intro t ht
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  cases u <;> exact ⟨pack_wellFormed _,pack_wellFormed _⟩
end NSSE.StoredQueryWellFormed
