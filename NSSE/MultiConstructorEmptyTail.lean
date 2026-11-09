import NSSE.MultiConstructorIsolatedPrefix

/-! Finite original token rows: joint emptiness is absorbing, and no
support-mediated birth can have an origin in the resulting empty tail. -/
namespace NSSE.MultiConstructorEmptyTail
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open MultiConstructorUnifiedWords MultiConstructorUnifiedPrefix
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem empty_after (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (J k : Nat) (he : row phi x y w J = (∅,∅)) (hJk : J ≤ k) (hkn : k ≤ w.length) :
    row phi x y w k = (∅,∅) := by
  induction k, hJk using Nat.le_induction with
  | base => exact he
  | succ k hJk ih =>
    rw [row_succ phi x y w k (by omega),ih (by omega)]
    exact Prod.ext (upperNext_empty phi _) (lowerNext_empty phi _)

theorem unpinned_next (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (k : Nat) (hk : k < w.length)
    (hu : upperPins phi (row phi x y w k).1 = ∅)
    (hl : lowerPins phi (row phi x y w k).2 = ∅) : row phi x y w (k+1) = (∅,∅) := by
  rw [row_succ phi x y w k hk]
  exact Prod.ext (upperNext_of_unpinned phi _ _ hu) (lowerNext_of_unpinned phi _ _ hl)

theorem root_nonempty (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) :
    row phi x y w 0 ≠ (∅,∅) := by
  intro he
  have hx : x ∈ (row phi x y w 0).1 :=
    (mem_up phi {x} x).mpr ⟨x,Finset.mem_singleton_self x,Support.refl x⟩
  rw [he] at hx
  exact Finset.not_mem_empty _ hx

theorem birth_before_empty (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (J a b : Nat) (he : row phi x y w J = (∅,∅)) (ha : a ≤ w.length) (hb : b ≤ w.length)
    (hborn : Born phi x y w a b) : a < J ∧ b < J := by
  obtain ⟨u,hu,v,hv,_⟩ := hborn
  constructor
  · by_contra h
    have he' := empty_after phi x y w J a he (by omega) ha
    rw [he'] at hu
    exact Finset.not_mem_empty _ hu
  · by_contra h
    have he' := empty_after phi x y w J b he (by omega) hb
    rw [he'] at hv
    exact Finset.not_mem_empty _ hv

end NSSE.MultiConstructorEmptyTail
