import NSSE.MultiVarianceFirstTail

/-! The selector follows its own signed frame. Before the first joint
empty position, local compatibility forces the supplied proper heads;
the sole unpinned position uses the last pre-empty head as fallback. -/
namespace NSSE.MultiVarianceSelectorTrace
open MultiConstructorConstraints (Query Constraints)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSelectorHead MultiVarianceSelectorStep MultiVarianceWordReader
open MultiVarianceWordEmptyTail
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def run (phi : Constraints arity n) (reset : Frame n) (fallback : H)
    (F : Frame n) (w : List (Letter arity)) : Frame n :=
  w.foldl (fun s a => next pol phi reset fallback s a.2.val) F

def trace (Q : Query arity n) (reset : Frame n) (fallback : H)
    (w : List (Letter arity)) (k : Nat) : Frame n :=
  run pol Q.constraints reset fallback (startFrame pol Q) (w.take k)

theorem trace_succ (Q : Query arity n) (reset : Frame n) (fallback : H)
    (w : List (Letter arity)) (k : Nat) (hk : k<w.length) :
    trace pol Q reset fallback w (k+1) =
      next pol Q.constraints reset fallback (trace pol Q reset fallback w k) w[k].2.val := by
  simp only [trace,run,List.take_succ_eq_append_getElem hk,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem proper_ready (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (hl : Local pol Q w ex ey) (k : Nat) (hk : k<w.length) :
    Ready Q.constraints (frame pol Q w k) w[k].1 := by
  have hx := hl k (Nat.le_of_lt hk) false
  have hy := hl k (Nat.le_of_lt hk) true
  simp only [value,List.getElem?_eq_getElem hk,roleOf,tokensOf,Bool.false_eq_true,if_false,if_true] at hx hy
  exact ⟨hx,hy⟩

theorem before_head (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (hl : Local pol Q w ex ey) (J : Nat) (hJ : 0<J) (hJn : J≤w.length)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k)) (k : Nat) (hk : k<J) :
    choose Q.constraints (frame pol Q w k) (w[J-1]'(by omega)).1 = (w[k]'(by omega)).1 := by
  have hkn : k<w.length := by omega
  by_cases hp : (framePins Q.constraints (frame pol Q w k)).Nonempty
  · exact choose_forced Q.constraints _ _ _ (proper_ready pol Q w ex ey hl k hkn) hp
  · have hp' := Finset.not_nonempty_iff_eq_empty.mp hp
    have he := unpinned_move_empty pol Q.constraints (frame pol Q w k) w[k].1 w[k].2 hp'
    rw [← frame_succ pol Q w k hkn] at he
    have hkJ : k+1=J := by
      by_contra h
      exact hbefore (k+1) (by omega) he
    rw [choose_unpinned Q.constraints _ _ hp']
    have hh : J-1=k := by omega
    subst k
    rfl

theorem before_empty (Q : Query arity n) (reset : Frame n) (fallback : H)
    (w : List (Letter arity)) (J : Nat) (hJn : J≤w.length)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k))
    (hheads : ∀ k, ∀ hk : k<J,
      choose Q.constraints (frame pol Q w k) fallback=(w[k]'(by omega)).1)
    (k : Nat) (hk : k<J) : trace pol Q reset fallback w k=frame pol Q w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k<w.length := by omega
    rw [trace_succ pol Q reset fallback w k hkn,ih (by omega)]
    have hs : step pol Q.constraints (frame pol Q w k)
        (choose Q.constraints (frame pol Q w k) fallback) w[k].2.val = frame pol Q w (k+1) := by
      rw [hheads k (by omega),step_valid]
      exact (frame_succ pol Q w k hkn).symm
    rw [next_raw pol Q.constraints reset fallback _ _ (by rw [hs]; exact hbefore (k+1) hk)]
    exact hs

theorem at_empty (Q : Query arity n) (reset : Frame n) (fallback : H)
    (w : List (Letter arity)) (J : Nat) (hJ : 0<J) (hJn : J≤w.length)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k))
    (hheads : ∀ k, ∀ hk : k<J,
      choose Q.constraints (frame pol Q w k) fallback=(w[k]'(by omega)).1)
    (he : Empty (frame pol Q w J)) : trace pol Q reset fallback w J=reset := by
  have hpred : J-1<w.length := by omega
  have hj : J-1+1=J := by omega
  have ht := trace_succ pol Q reset fallback w (J-1) hpred
  rw [hj,before_empty pol Q reset fallback w J hJn hbefore hheads (J-1) (by omega)] at ht
  rw [ht]
  apply next_reset
  rw [hheads (J-1) (by omega),step_valid,← frame_succ pol Q w (J-1) hpred,hj]
  exact he

end NSSE.MultiVarianceSelectorTrace
