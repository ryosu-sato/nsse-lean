import NSSE.P0SuffixRank

/-! At equal proper states, a four-rail conflict is exactly literal suffix
nesting. Completeness and distinct endpoint labels suffice; safety and
the birth relation are not premises. -/
namespace NSSE.P0SuffixConflict
open P0DZBranch P0DZTrace P0ProperWords P0SuffixRank
variable {Q Z A H : Type*}

theorem match_iff_prefix (w : List A) (a b : Nat) (hab : a ≤ b) (hb : b ≤ w.length) :
    WordMatch w a b (w.length-b) ↔ (w.drop b).IsPrefix (w.drop a) := by
  rw [List.isPrefix_iff_getElem]
  constructor
  · intro hm
    refine ⟨by simp only [List.length_drop]; omega,?_⟩
    intro i hi
    have hi' : i < w.length-b := by simpa only [List.length_drop] using hi
    have hh := hm i hi'
    rw [List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem (by omega),
      Option.some.injEq] at hh
    simpa only [List.getElem_drop] using hh.symm
  · rintro ⟨hlen,h⟩ i hi
    have hh := h i (by simpa only [List.length_drop] using hi)
    simp only [List.getElem_drop] at hh
    rw [List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem (by omega)]
    exact congrArg some hh.symm

def AllCompatible (J : Branch Q Z A H) (w : List A) (a b : Nat) : Prop :=
  ∀ s t, Compatible J w a s b t

theorem nested_conflict (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a b : Nat) (hab : a < b) (hb : b ≤ w.length)
    (hp : (w.drop b).IsPrefix (w.drop a)) : ¬ AllCompatible J w a b := by
  intro h
  have hm := (match_iff_prefix w a b (by omega) hb).mpr hp
  have hx := h false false (w.length-b) (by omega) (by omega) (by omega) hm
  have hy := h false true (w.length-b) (by omega) (by omega) (by omega) hm
  have hbn : b+(w.length-b) = w.length := by omega
  rw [hbn,label_terminal J w hc false] at hx
  rw [hbn,label_terminal J w hc true] at hy
  exact hends ((agree_eq hx).symm.trans (agree_eq hy))

theorem nonnested_compatible (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (hab : a < b) (hb : b < w.length)
    (he : properAt J w a = properAt J w b)
    (hp : ¬ (w.drop b).IsPrefix (w.drop a)) : AllCompatible J w a b := by
  intro s t l _ hla hlb hm
  have hstrict : b+l < w.length := by
    by_contra hn
    have heq : l = w.length-b := by omega
    subst l
    exact hp ((match_iff_prefix w a b (by omega) (by omega)).mp hm)
  have heq := proper_equal J w a b l hla hlb he hm
  obtain ⟨q,hq⟩ := complete_prefix J w hc (a+l) (by omega)
  rw [label_proper J w (a+l) (by omega) q hq s,
    label_proper J w (b+l) hstrict q (heq.symm.trans hq) t]
  rfl

theorem all_iff (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a b : Nat) (hab : a < b) (hb : b < w.length)
    (he : properAt J w a = properAt J w b) :
    AllCompatible J w a b ↔ ¬ (w.drop b).IsPrefix (w.drop a) := by
  exact ⟨fun h hp => nested_conflict J w hc hends a b hab (by omega) hp h,
    nonnested_compatible J w hc a b hab hb he⟩

theorem conflict_iff_linked (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a b : Nat) (hab : a < b) (hb : b < w.length)
    (he : properAt J w a = properAt J w b) :
    ¬ AllCompatible J w a b ↔ Linked J w a b := by
  rw [all_iff J w hc hends a b hab hb he,not_not]
  exact ⟨fun hp => ⟨hab,hb,he,hp⟩,fun h => h.2.2.2⟩

end NSSE.P0SuffixConflict
