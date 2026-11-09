import NSSE.P0SuffixCotree

/-! A symmetric module in the suffix graph is an ordered-color module.
For nonadjacent vertices, equality of symmetric external adjacency already
forces equality of both directed comparison bits. This lets union/join
tree modules retain the direction-sensitive information needed by cuts. -/
namespace NSSE.P0SuffixOrientation
open P0SuffixWords P0SuffixMatrix P0SuffixCotree
variable {A H : Type*}

theorem rels_of_nonedge (endX endY : H) (s t : List (H × A)) (hn : ¬ Edge endX endY s t) :
    Rel endX endY s t ∧ Rel endX endY t s := by
  simpa only [Edge,not_or,not_not] using hn

theorem both_nonedge (endX endY : H) (s t z : List (H × A))
    (hs : ¬ Edge endX endY s z) (ht : ¬ Edge endX endY t z) :
    (Rel endX endY s z ↔ Rel endX endY t z) ∧
    (Rel endX endY z s ↔ Rel endX endY z t) := by
  have hh := rels_of_nonedge endX endY s z hs
  have hk := rels_of_nonedge endX endY t z ht
  exact ⟨iff_of_true hh.1 hk.1,iff_of_true hh.2 hk.2⟩

theorem uniform (endX endY : H) (hne : endX ≠ endY) (s t z : List (H × A))
    (hn : ¬ Edge endX endY s t)
    (he : Edge endX endY s z ↔ Edge endX endY t z) :
    (Rel endX endY s z ↔ Rel endX endY t z) ∧
    (Rel endX endY z s ↔ Rel endX endY z t) := by
  classical
  induction s generalizing t z with
  | nil =>
    have hh := rels_of_nonedge endX endY [] t hn
    cases t with
    | nil => exact False.elim (hne hh.1)
    | cons x t => exact False.elim (hne (hh.1.trans hh.2))
  | cons x s ih =>
    obtain ⟨h,a⟩ := x
    have hh := rels_of_nonedge endX endY ((h,a)::s) t hn
    cases t with
    | nil => exact False.elim (hne (hh.2.trans hh.1))
    | cons x t =>
      obtain ⟨k,b⟩ := x
      have hhk : h = k := hh.1.1
      subst k
      cases z with
      | nil => exact ⟨Iff.rfl,Iff.rfl⟩
      | cons x z =>
        obtain ⟨k,c⟩ := x
        by_cases hhk : h = k
        · subst k
          by_cases hab : a = b
          · subst b
            by_cases hac : a = c
            · subst c
              have hn' : ¬ Edge endX endY s t := by simpa only [Edge,same_letter] using hn
              have he' : Edge endX endY s z ↔ Edge endX endY t z := by
                simpa only [Edge,same_letter] using he
              simpa only [same_letter] using ih t z hn' he'
            · simp [Rel,hac,Ne.symm hac]
          · by_cases hac : a = c
            · have hbc : b ≠ c := by intro hbc; exact hab (hac.trans hbc.symm)
              have htz : ¬ Edge endX endY ((h,b)::t) ((h,c)::z) := by
                simp [Edge,Rel,hbc,Ne.symm hbc]
              exact both_nonedge endX endY _ _ _ (fun h => htz (he.mp h)) htz
            · have hsz : ¬ Edge endX endY ((h,a)::s) ((h,c)::z) := by
                simp [Edge,Rel,hac,Ne.symm hac]
              exact both_nonedge endX endY _ _ _ hsz (fun h => hsz (he.mpr h))
        · simp [Rel,hhk,Ne.symm hhk]

end NSSE.P0SuffixOrientation
