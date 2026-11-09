import NSSE.MultiConstructorSelectorReplay

/-! The fallback head immediately before erasure handles the only free
pre-empty position. Reset replay then reproduces every assigned proper head. -/
namespace NSSE.MultiConstructorSelectorHeads
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawValidity
open MultiConstructorUnifiedWords MultiConstructorEmptyTail MultiConstructorTailPeriod
open MultiConstructorSelectorHead MultiConstructorSelectorTrace MultiConstructorSelectorReplay
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem proper_row (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (hl : Local phi x y w heads) (k : Nat) (hk : k < w.length) :
    Proper phi (row phi x y w k) :=
  ⟨(hl ⟨k,hk⟩).1,compatible_card phi _ _ (hl ⟨k,hk⟩).2.1⟩

theorem before_head (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (hl : Local phi x y w heads) (J : Nat)
    (hJ : 0 < J) (hJn : J ≤ w.length)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅))
    (k : Nat) (hk : k < J) :
    choose phi (row phi x y w k) (heads ⟨J-1,by omega⟩) = heads ⟨k,by omega⟩ := by
  have hc := (hl ⟨k,by omega⟩).2.1
  by_cases hp : (pins phi (row phi x y w k)).Nonempty
  · obtain ⟨g,hg⟩ := hp
    exact (choose_forced phi _ _ g (compatible_card phi _ _ hc) hg).trans (hc g hg)
  · have hp' : pins phi (row phi x y w k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    have hs := Finset.union_eq_empty.mp hp'
    have he := unpinned_next phi x y w k (by omega) hs.1 hs.2
    have hkJ : k+1 = J := by
      by_contra h
      exact hbefore (k+1) (by omega) he
    rw [choose_unpinned phi _ _ hp']
    congr 1
    apply Fin.ext
    change J-1 = k
    omega

theorem replay_head (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (hl : Local phi x y w heads) (J d : Nat)
    (hJ : J < w.length) (hd : 0 < d) (hdJ : d < J)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅))
    (he : row phi x y w J = (∅,∅)) (hc : Copied w heads J d)
    (k : Nat) (hkn : k < w.length) :
    choose phi (trace phi x y (row phi x y w (J-d)) w k) (heads ⟨J-1,by omega⟩) =
      heads ⟨k,hkn⟩ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkJ : k < J
    · rw [before_empty phi x y _ w J (by omega) hbefore k hkJ]
      exact before_head phi x y w heads hl J (by omega) (by omega) hbefore k hkJ
    · rw [state_period phi x y w heads J d hJ hd hdJ hbefore he hc k (by omega) hkn,
        ih (k-d) (by omega) (by omega)]
      exact hc.2 ⟨k,hkn⟩ (by change J ≤ k; omega)

theorem replay_proper (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (hl : Local phi x y w heads) (J d : Nat)
    (hJ : J < w.length) (hd : 0 < d) (hdJ : d < J)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅))
    (he : row phi x y w J = (∅,∅)) (hc : Copied w heads J d)
    (k : Nat) (hkn : k < w.length) :
    Proper phi (trace phi x y (row phi x y w (J-d)) w k) := by
  obtain ⟨r,hr,heq⟩ := old_row phi x y w heads J d hJ hd hdJ hbefore he hc k hkn
  rw [heq]
  exact proper_row phi x y w heads hl r (by omega)

end NSSE.MultiConstructorSelectorHeads
