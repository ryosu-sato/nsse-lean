import NSSE.MultiVarianceFirstPrefix

/-! Actual signed tokens stay jointly empty, although their raw sign
may continue changing. Every birth of a surviving ray predates that
empty tail. Accepted separating words have no same-position birth. -/
namespace NSSE.MultiVarianceWordEmptyTail
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact MultiVarianceBranch
open MultiVarianceWordReader MultiVarianceWordPrefix MultiVarianceFirstPrefix MultiVarianceSelectorHead
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem frame_succ (Q : Query arity n) (w : List (Letter arity)) (k : Nat) (hk : k<w.length) :
    frame pol Q w (k+1)=physicalMove pol Q.constraints (frame pol Q w k) w[k].1 w[k].2 := by
  unfold frame
  rw [List.take_succ_eq_append_getElem hk,MultiVariancePhysicalTrace.runPhysical_append]
  rfl

theorem empty_after (Q : Query arity n) (w : List (Letter arity)) (J k : Nat)
    (he : Empty (frame pol Q w J)) (hJk : J ≤ k) (hk : k ≤ w.length) : Empty (frame pol Q w k) := by
  induction k, hJk using Nat.le_induction with
  | base => exact he
  | succ k hJk ih =>
    have he' := ih (by omega)
    rw [frame_succ pol Q w k (by omega)]
    exact unpinned_move_empty pol Q.constraints _ _ _ (empty_pins Q.constraints _ he')

theorem root_nonempty (Q : Query arity n) (w : List (Letter arity)) : ¬Empty (frame pol Q w 0) := by
  intro he
  have hx : Q.left ∈ (frame pol Q w 0).x := MultiVarianceModelTokens.up_self pol Q.constraints Q.left
  rw [he.1] at hx
  exact Finset.not_mem_empty _ hx

theorem empty_left_no_birth (F G : Frame n) (he : Empty F) (s t : Bool) : ¬RawBirth F s G t := by
  have ht : tokensOf F s=∅ := by cases s <;> first | exact he.1 | exact he.2
  simp [RawBirth,inspectBirth,ht]

theorem empty_right_no_birth (F G : Frame n) (he : Empty G) (s t : Bool) : ¬RawBirth F s G t := by
  have ht : tokensOf G t=∅ := by cases t <;> first | exact he.1 | exact he.2
  simp [RawBirth,inspectBirth,ht]

theorem birth_before_empty (Q : Query arity n) (w : List (Letter arity)) (J a b : Nat)
    (he : Empty (frame pol Q w J)) (ha : a ≤ w.length) (hb : b ≤ w.length) (s t : Bool)
    (hborn : Born pol Q w a s b t) : a<J ∧ b<J := by
  constructor
  · by_contra hh
    exact empty_left_no_birth _ _ (empty_after pol Q w J a he (by omega) ha) s t hborn
  · by_contra hh
    exact empty_right_no_birth _ _ (empty_after pol Q w J b he (by omega) hb) s t hborn

theorem symBorn_before_empty (Q : Query arity n) (w : List (Letter arity)) (J a b : Nat)
    (he : Empty (frame pol Q w J)) (ha : a ≤ w.length) (hb : b ≤ w.length) (s t : Bool)
    (hborn : SymBorn pol Q w a s b t) : a<J ∧ b<J := by
  rcases hborn with hh | hh
  · exact birth_before_empty pol Q w J a b he ha hb s t hh
  · exact (birth_before_empty pol Q w J b a he hb ha t s hh).symm

theorem valid_ends_distinct (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (hv : ValidEnd pol Q w ex ey) : ex ≠ ey := by
  intro he
  unfold ValidEnd at hv
  rw [he] at hv
  simp only [ite_self] at hv
  exact hv le_rfl

theorem no_diagonal_birth (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (hw : Accepted pol Q w ex ey) (a : Nat) (ha : a ≤ w.length) (s t : Bool) :
    ¬Born pol Q w a s a t := by
  intro hb
  have hst : s ≠ t := by
    intro he
    subst t
    exact no_same_vertex_birth _ s hb
  have hsum : a+(w.length-a)=w.length := Nat.add_sub_of_le ha
  have hh := hw.2.2.2 a ha a ha s t hb (w.length-a) (by omega) (by omega) (fun _ _ => rfl)
  rw [hsum,value,List.getElem?_length,value,List.getElem?_length] at hh
  have he : ex=ey := by
    cases s <;> cases t
    · exact False.elim (hst rfl)
    · exact P0DZTrace.agree_eq hh
    · exact (P0DZTrace.agree_eq hh).symm
    · exact False.elim (hst rfl)
  exact valid_ends_distinct pol Q w ex ey hw.1 he

theorem no_diagonal_symBorn (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (hw : Accepted pol Q w ex ey) (a : Nat) (ha : a ≤ w.length) (s t : Bool) :
    ¬SymBorn pol Q w a s a t := by
  rintro (hb | hb)
  · exact no_diagonal_birth pol Q w ex ey hw a ha s t hb
  · exact no_diagonal_birth pol Q w ex ey hw a ha t s hb

end NSSE.MultiVarianceWordEmptyTail
