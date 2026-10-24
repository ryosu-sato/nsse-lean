import NSSE.CapAlphabetImage

/-! Padding alphabets while covering precisely the newly introduced words. -/

namespace NSSE.CapAlphabetPadding

open CapAlphabetImage

variable {α β : Type*} (f : α → β)

def foreign : Language β := fun ys => ¬ ∃ xs : List α, xs.map f = ys

def pad (E : CapExpression α) : CapExpression β where
  caps := E.caps.map (component f)
  routes := foreign f :: E.routes.map (image f)

theorem route_at_map (hf : Function.Injective f) (L : Language α) (xs : List α) :
    Language.concat (image f L) Language.univ (xs.map f) ↔
      Language.concat L Language.univ xs := by
  constructor
  · rintro ⟨u,v,he,⟨ys,hy,hyu⟩,_⟩
    obtain ⟨a,b,hab,ha,hb⟩ := List.map_eq_append_iff.mp he
    have heq := (List.map_injective_iff.mpr hf) (hyu.trans ha.symm)
    exact ⟨a,b,hab,by simpa only [heq] using hy,trivial⟩
  · rintro ⟨u,v,rfl,hu,_⟩
    exact ⟨u.map f,v.map f,List.map_append,⟨u,hu,rfl⟩,trivial⟩

theorem foreign_route_not_map (xs : List α) :
    ¬ Language.concat (foreign f) Language.univ (xs.map f) := by
  rintro ⟨u,v,he,hforeign,_⟩
  obtain ⟨a,b,hab,ha,hb⟩ := List.map_eq_append_iff.mp he
  exact hforeign ⟨a,ha⟩

theorem capCovered_at_map (hf : Function.Injective f) (E : CapExpression α) (xs : List α) :
    capCovered (pad f E) (xs.map f) ↔ capCovered E xs := by
  simp only [capCovered, pad, List.mem_map]
  constructor
  · rintro ⟨c,⟨a,ha,rfl⟩,hc⟩
    exact ⟨a,ha,(image_at_map f hf _ xs).mp ((component_image f a _).mp hc)⟩
  · rintro ⟨c,hc,hw⟩
    exact ⟨component f c,⟨c,hc,rfl⟩,(component_image f c _).mpr ((image_at_map f hf _ xs).mpr hw)⟩

theorem routeCovered_at_map (hf : Function.Injective f) (E : CapExpression α) (xs : List α) :
    routeCovered (pad f E) (xs.map f) ↔ routeCovered E xs := by
  constructor
  · rintro ⟨R,hR,hw⟩
    rcases List.mem_cons.mp hR with rfl | hR
    · exact False.elim (foreign_route_not_map f xs hw)
    · obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hR
      exact ⟨L,hL,(route_at_map f hf L xs).mp hw⟩
  · rintro ⟨L,hL,hw⟩
    exact ⟨image f L,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨L,hL,rfl⟩),(route_at_map f hf L xs).mpr hw⟩

theorem uncovered_at_map (hf : Function.Injective f) (E : CapExpression α) (xs : List α) :
    (pad f E).Uncovered (xs.map f) ↔ E.Uncovered xs := by
  unfold CapExpression.Uncovered CapExpression.Covers
  rw [capCovered_at_map f hf, routeCovered_at_map f hf]

theorem uncovered_iff (hf : Function.Injective f) (E : CapExpression α) (ys : List β) :
    (pad f E).Uncovered ys ↔ ∃ xs : List α, xs.map f = ys ∧ E.Uncovered xs := by
  constructor
  · intro hu
    have himage : ∃ xs : List α, xs.map f = ys := by
      classical
      by_contra h
      apply hu
      exact Or.inr ⟨foreign f,by simp [pad],ys,[],by simp,h,trivial⟩
    obtain ⟨xs,rfl⟩ := himage
    exact ⟨xs,rfl,(uncovered_at_map f hf E xs).mp hu⟩
  · rintro ⟨xs,rfl,hu⟩
    exact (uncovered_at_map f hf E xs).mpr hu

theorem exists_uncovered_iff (hf : Function.Injective f) (E : CapExpression α) :
    (∃ ys, (pad f E).Uncovered ys) ↔ ∃ xs, E.Uncovered xs := by
  simp only [uncovered_iff f hf]
  constructor
  · rintro ⟨ys,xs,_,hu⟩; exact ⟨xs,hu⟩
  · rintro ⟨xs,hu⟩; exact ⟨xs.map f,xs,rfl,hu⟩

end NSSE.CapAlphabetPadding
