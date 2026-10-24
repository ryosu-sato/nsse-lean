import NSSE.StoredSubterms

namespace NSSE.StoredSubtermWeight
open StoredSubtypeTerm StoredSubterms
variable {n : Nat}

theorem bound (t : Term n) : ∀ u ∈ (subterms t).1, weight u ≤ weight t := by
  apply subterms.induct
    (motive1 := fun t => ∀ u ∈ (subterms t).1, weight u ≤ weight t)
    (motive2 := fun ts => ∀ u ∈ (forest ts).1, weight u ≤ forestWeight ts)
  · intro x u hu; simp only [subterms,List.mem_singleton] at hu; subst u; rfl
  · intro u hu; simp only [subterms,List.mem_singleton] at hu; subst u; rfl
  · intro u hu; simp only [subterms,List.mem_singleton] at hu; subst u; rfl
  · intro cs ih u hu
    simp only [subterms,List.mem_cons] at hu
    rcases hu with rfl | hu
    · rfl
    · have h := ih u hu
      simp only [weight]; change weight u ≤ 1+forestWeight cs; omega
  · intro u hu; simp [forest] at hu
  · intro t ts ha hb u hu
    simp only [forest,CountedListConstruction.append_value,List.mem_append] at hu
    simp only [forestWeight,List.map_cons,List.sum_cons]
    change weight u ≤ 1+weight t+forestWeight ts
    rcases hu with hu | hu
    · have h := ha u hu; omega
    · have h := hb u hu; omega
end NSSE.StoredSubtermWeight
