import NSSE.P0SuffixOrientation

/-! A nonedge for distinct base endpoints means that comparison stops at
a proper letter divergence. It therefore implies comparison for ANY
endpoint pair, and symmetric cotree modules retain all four rail bits. -/
namespace NSSE.P0FourRailOrientation
open P0SuffixWords P0SuffixMatrix P0SuffixCotree P0SuffixOrientation
variable {A H : Type*}

theorem rel_self (x y : H) (s : List (H × A)) : Rel x y s s ↔ x = y := by
  induction s with
  | nil => rfl
  | cons p s ih => obtain ⟨h,a⟩ := p; simpa only [same_letter] using ih

theorem nonedge_any (endX endY : H) (hne : endX ≠ endY)
    (s t : List (H × A)) (hn : ¬ Edge endX endY s t) (x y : H) : Rel x y s t := by
  induction s generalizing t with
  | nil =>
    have hh := rels_of_nonedge endX endY [] t hn
    cases t with
    | nil => exact False.elim (hne hh.1)
    | cons p t => exact False.elim (hne (hh.1.trans hh.2))
  | cons p s ih =>
    obtain ⟨h,a⟩ := p
    have hh := rels_of_nonedge endX endY ((h,a)::s) t hn
    cases t with
    | nil => exact False.elim (hne (hh.2.trans hh.1))
    | cons p t =>
      obtain ⟨k,b⟩ := p
      have hhk : h = k := hh.1.1
      subst k
      refine ⟨rfl,?_⟩
      intro hab
      subst b
      apply ih t
      simpa only [Edge,same_letter] using hn

theorem both_nonedge_any (endX endY : H) (hne : endX ≠ endY) (s t z : List (H × A))
    (hs : ¬ Edge endX endY s z) (ht : ¬ Edge endX endY t z) (x y : H) :
    (Rel x y s z ↔ Rel x y t z) ∧ (Rel x y z s ↔ Rel x y z t) := by
  have hzs : ¬ Edge endX endY z s := by simpa only [Edge,or_comm] using hs
  have hzt : ¬ Edge endX endY z t := by simpa only [Edge,or_comm] using ht
  exact ⟨iff_of_true (nonedge_any endX endY hne s z hs x y)
    (nonedge_any endX endY hne t z ht x y),
    iff_of_true (nonedge_any endX endY hne z s hzs x y)
    (nonedge_any endX endY hne z t hzt x y)⟩

theorem uniform (endX endY : H) (hne : endX ≠ endY) (s t z : List (H × A))
    (hn : ¬ Edge endX endY s t)
    (he : Edge endX endY s z ↔ Edge endX endY t z) (x y : H) :
    (Rel x y s z ↔ Rel x y t z) ∧ (Rel x y z s ↔ Rel x y z t) := by
  classical
  induction s generalizing t z with
  | nil =>
    have hh := rels_of_nonedge endX endY [] t hn
    cases t with
    | nil => exact False.elim (hne hh.1)
    | cons p t => exact False.elim (hne (hh.1.trans hh.2))
  | cons p s ih =>
    obtain ⟨h,a⟩ := p
    have hh := rels_of_nonedge endX endY ((h,a)::s) t hn
    cases t with
    | nil => exact False.elim (hne (hh.2.trans hh.1))
    | cons p t =>
      obtain ⟨k,b⟩ := p
      have hhk : h = k := hh.1.1
      subst k
      cases z with
      | nil => exact ⟨Iff.rfl,Iff.rfl⟩
      | cons p z =>
        obtain ⟨k,c⟩ := p
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
              exact both_nonedge_any endX endY hne _ _ _ (fun h => htz (he.mp h)) htz x y
            · have hsz : ¬ Edge endX endY ((h,a)::s) ((h,c)::z) := by
                simp [Edge,Rel,hac,Ne.symm hac]
              exact both_nonedge_any endX endY hne _ _ _ hsz (fun h => hsz (he.mpr h)) x y
        · simp [Rel,hhk,Ne.symm hhk]

end NSSE.P0FourRailOrientation
