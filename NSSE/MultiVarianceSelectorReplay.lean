import NSSE.MultiVarianceSelectorTrace

/-! Literal copied tails replay whole selector frames, including their
own signs. No equality between raw and selector signs after reset is used.
The final exceptional child is deliberately outside the copied letters. -/
namespace NSSE.MultiVarianceSelectorReplay
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceSelectorHead
open MultiVarianceWordReader MultiVarianceFirstTail MultiVarianceSelectorTrace
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem state_period (Q : Query arity n) (w : List (Letter arity)) (fallback : H)
    (J d : Nat) (hJ : J<w.length) (hd : 0<d) (hdJ : d<J)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k))
    (hheads : ∀ k, ∀ hk : k<J,
      choose Q.constraints (frame pol Q w k) fallback=(w[k]'(by omega)).1)
    (he : Empty (frame pol Q w J)) (hc : Copied w J d)
    (k : Nat) (hJk : J≤k) (hkn : k<w.length) :
    trace pol Q (frame pol Q w (J-d)) fallback w k =
      trace pol Q (frame pol Q w (J-d)) fallback w (k-d) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkJ : k=J
    · subst k
      rw [at_empty pol Q _ fallback w J (by omega) (by omega) hbefore hheads he,
        before_empty pol Q _ fallback w J (by omega) hbefore hheads (J-d) (by omega)]
    · have hpred : k-1<w.length := by omega
      have hpredd : k-1-d<w.length := by omega
      have h1 : k-1+1=k := by omega
      have h2 : k-1-d+1=k-d := by omega
      have hs := ih (k-1) (by omega) (by omega) hpred
      have hl := hc.1 (k-1) (by omega) (by omega)
      rw [List.getElem?_eq_getElem hpredd,List.getElem?_eq_getElem hpred] at hl
      have hletter := congrArg (fun a : Letter arity => a.2.val) (Option.some.inj hl)
      dsimp only at hletter
      have ht := trace_succ pol Q (frame pol Q w (J-d)) fallback w (k-1) hpred
      have ht' := trace_succ pol Q (frame pol Q w (J-d)) fallback w (k-1-d) hpredd
      rw [h1,hs,← hletter] at ht
      rw [h2] at ht'
      exact ht.trans ht'.symm

theorem old_frame (Q : Query arity n) (w : List (Letter arity)) (fallback : H)
    (J d : Nat) (hJ : J<w.length) (hd : 0<d) (hdJ : d<J)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k))
    (hheads : ∀ k, ∀ hk : k<J,
      choose Q.constraints (frame pol Q w k) fallback=(w[k]'(by omega)).1)
    (he : Empty (frame pol Q w J)) (hc : Copied w J d)
    (k : Nat) (hkn : k<w.length) :
    ∃ r, r<J ∧ trace pol Q (frame pol Q w (J-d)) fallback w k=frame pol Q w r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkJ : k<J
    · exact ⟨k,hkJ,before_empty pol Q _ fallback w J (by omega) hbefore hheads k hkJ⟩
    · obtain ⟨r,hr,heq⟩ := ih (k-d) (by omega) (by omega)
      exact ⟨r,hr,(state_period pol Q w fallback J d hJ hd hdJ hbefore hheads he hc k (by omega) hkn).trans heq⟩

theorem replay_head (Q : Query arity n) (w : List (Letter arity)) (fallback : H)
    (J d : Nat) (hJ : J<w.length) (hd : 0<d) (hdJ : d<J)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k))
    (hheads : ∀ k, ∀ hk : k<J,
      choose Q.constraints (frame pol Q w k) fallback=(w[k]'(by omega)).1)
    (he : Empty (frame pol Q w J)) (hc : Copied w J d)
    (k : Nat) (hkn : k<w.length) :
    choose Q.constraints (trace pol Q (frame pol Q w (J-d)) fallback w k) fallback=w[k].1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkJ : k<J
    · rw [before_empty pol Q _ fallback w J (by omega) hbefore hheads k hkJ]
      exact hheads k hkJ
    · rw [state_period pol Q w fallback J d hJ hd hdJ hbefore hheads he hc k (by omega) hkn,
        ih (k-d) (by omega) (by omega)]
      exact hc.2 k hkn (by omega)

theorem replay_ready (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (hl : Local pol Q w ex ey) (fallback : H)
    (J d : Nat) (hJ : J<w.length) (hd : 0<d) (hdJ : d<J)
    (hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k))
    (hheads : ∀ k, ∀ hk : k<J,
      choose Q.constraints (frame pol Q w k) fallback=(w[k]'(by omega)).1)
    (he : Empty (frame pol Q w J)) (hc : Copied w J d)
    (k : Nat) (hkn : k<w.length) :
    Ready Q.constraints (trace pol Q (frame pol Q w (J-d)) fallback w k) w[k].1 := by
  obtain ⟨r,hr,heq⟩ := old_frame pol Q w fallback J d hJ hd hdJ hbefore hheads he hc k hkn
  have hh := replay_head pol Q w fallback J d hJ hd hdJ hbefore hheads he hc k hkn
  rw [heq,hheads r hr] at hh
  rw [heq,← hh]
  exact proper_ready pol Q w ex ey hl r (by omega)

end NSSE.MultiVarianceSelectorReplay
