import NSSE.Cap

/-! # A common suffix turns prefix overlap into a genuine power prefix

The same root and anchor are retained. The empty-root alternative is
separate; no positive root or exponent is manufactured for that case.
-/

namespace NSSE.CommonSuffixPeriod

universe u
variable {α : Type u}

theorem self_overlap_power (s r : List α) (hs : s ≠ []) (h : r <+: s ++ r) :
    ∃ k, s ++ r <+: Language.wordPower s k := by
  by_cases hr : r = []
  · subst r
    exact ⟨1,by simp [Language.wordPower]⟩
  · have hp : Word.HasPeriod (s ++ r) s.length := by
      constructor
      · have hrl := List.length_pos_iff.mpr hr
        simp only [List.length_append]
        omega
      · have he := (List.prefix_iff_eq_take.mp h).symm
        have hlen : s.length + r.length - s.length = r.length := by omega
        simpa [Word.factor, hlen] using he
    obtain ⟨k,tail,hk⟩ := Language.hasPeriod_prefix_wordPower (s ++ r) s.length
      (List.length_pos_iff.mpr hs) hp
    have hk' : Language.wordPower s k = (s ++ r) ++ tail := by simpa using hk
    refine ⟨k,?_⟩
    rw [hk']
    exact List.prefix_append _ _

theorem overlap_split (a b r : List α) (h : a ++ r <+: b ++ r) :
    ∃ s, b = a ++ s ∧ r <+: s ++ r := by
  have hab : a.length ≤ b.length := by
    have hl := h.length_le
    simp only [List.length_append] at hl
    omega
  have hp : a <+: b := List.prefix_of_prefix_length_le
    ((List.prefix_append a r).trans h) (List.prefix_append b r) hab
  obtain ⟨s,rfl⟩ := hp
  refine ⟨s,rfl,?_⟩
  apply (List.prefix_append_right_inj a).mp
  simpa only [List.append_assoc] using h

theorem overlap_periodic (a b r : List α) (h : a ++ r <+: b ++ r) :
    ∃ s, b = a ++ s ∧ (s = [] ∨ ∃ k, b ++ r <+: a ++ Language.wordPower s k) := by
  obtain ⟨s,rfl,hr⟩ := overlap_split a b r h
  refine ⟨s,rfl,?_⟩
  by_cases hs : s = []
  · exact Or.inl hs
  · obtain ⟨k,hk⟩ := self_overlap_power s r hs hr
    exact Or.inr ⟨k,by simpa only [List.append_assoc] using (List.prefix_append_right_inj a).mpr hk⟩

end NSSE.CommonSuffixPeriod
