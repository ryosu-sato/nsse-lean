import NSSE.MultiConstructorSelectorTrace

/-! A literal copied tail makes the deterministic reset selector repeat
the old segment. Every proper selector state is an old pre-empty raw row. -/
namespace NSSE.MultiConstructorSelectorReplay
open MultiConstructorConstraints MultiConstructorUnifiedWords MultiConstructorTailPeriod
open MultiConstructorSelectorTrace
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem state_period (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (J d : Nat) (hJ : J < w.length) (hd : 0 < d) (hdJ : d < J)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅))
    (he : row phi x y w J = (∅,∅)) (hc : Copied w heads J d)
    (k : Nat) (hJk : J ≤ k) (hkn : k < w.length) :
    trace phi x y (row phi x y w (J-d)) w k =
      trace phi x y (row phi x y w (J-d)) w (k-d) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkJ : k = J
    · subst k
      rw [at_empty phi x y _ w J (by omega) (by omega) hbefore he,
        before_empty phi x y _ w J (by omega) hbefore (J-d) (by omega)]
    · have hpred : k-1 < w.length := by omega
      have hpredd : k-1-d < w.length := by omega
      have h1 : k-1+1 = k := by omega
      have h2 : k-1-d+1 = k-d := by omega
      have hs := ih (k-1) (by omega) (by omega) hpred
      have hl := hc.1 (k-1) (by omega) (by omega)
      rw [List.getElem?_eq_getElem hpredd,List.getElem?_eq_getElem hpred] at hl
      have hletter := congrArg Fin.val (Option.some.inj hl)
      have ht := trace_succ phi x y (row phi x y w (J-d)) w (k-1) hpred
      have ht' := trace_succ phi x y (row phi x y w (J-d)) w (k-1-d) hpredd
      rw [h1,hs,← hletter] at ht
      rw [h2] at ht'
      exact ht.trans ht'.symm

theorem old_row (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (J d : Nat) (hJ : J < w.length) (hd : 0 < d) (hdJ : d < J)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅))
    (he : row phi x y w J = (∅,∅)) (hc : Copied w heads J d)
    (k : Nat) (hkn : k < w.length) :
    ∃ r, r < J ∧ trace phi x y (row phi x y w (J-d)) w k = row phi x y w r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkJ : k < J
    · exact ⟨k,hkJ,before_empty phi x y _ w J (by omega) hbefore k hkJ⟩
    · obtain ⟨r,hr,heq⟩ := ih (k-d) (by omega) (by omega)
      exact ⟨r,hr,(state_period phi x y w heads J d hJ hd hdJ hbefore he hc k (by omega) hkn).trans heq⟩

end NSSE.MultiConstructorSelectorReplay
