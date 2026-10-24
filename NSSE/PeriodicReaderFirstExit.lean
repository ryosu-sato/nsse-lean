import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega
import NSSE.BoundedPrefixPeriodicOverlap

/-! A first exit of a deterministic finite reader has no repeated state.
Applying this to reader state × periodic-word phase gives a bound for all
branching readers. It is a LOCAL exit bound, not a global overlap bound. -/
namespace NSSE.PeriodicReaderFirstExit
variable {S : Type*}

theorem equal_shift (next : S → S) (run : Nat → S)
    (hstep : ∀ k, run (k+1) = next (run k))
    (a b : Nat) (hab : run a = run b) (d : Nat) :
    run (a+d) = run (b+d) := by
  induction d with
  | zero => simpa using hab
  | succ d ih =>
    rw [show a+(d+1) = (a+d)+1 by omega,
        show b+(d+1) = (b+d)+1 by omega,hstep,hstep,ih]

theorem first_exit_injective (next : S → S) (run : Nat → S)
    (stop : S → Prop) (n : Nat)
    (hstep : ∀ k, run (k+1) = next (run k))
    (hend : stop (run n)) (hfirst : ∀ k, k < n → ¬ stop (run k)) :
    Function.Injective (fun k : Fin (n+1) => run k.val) := by
  intro a b heq
  have exclude : ∀ i j, i < j → j ≤ n → run i = run j → False := by
    intro i j hij hj he
    have shifted := equal_shift next run hstep i j he (n-j)
    have hsum : j+(n-j) = n := by omega
    rw [hsum] at shifted
    have hs : stop (run (i+(n-j))) := shifted ▸ hend
    exact hfirst (i+(n-j)) (by omega) hs
  have hav := a.isLt
  have hbv := b.isLt
  apply Fin.ext
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact exclude a.val b.val hlt (by omega) heq
  · exact exclude b.val a.val hgt (by omega) heq.symm

theorem first_exit_bound [Fintype S] (next : S → S) (run : Nat → S)
    (stop : S → Prop) (n : Nat)
    (hstep : ∀ k, run (k+1) = next (run k))
    (hend : stop (run n)) (hfirst : ∀ k, k < n → ¬ stop (run k)) :
    n+1 ≤ Fintype.card S := by
  have h := Fintype.card_le_of_injective (fun k : Fin (n+1) => run k.val)
    (first_exit_injective next run stop n hstep hend hfirst)
  simpa using h

/-- Includes the terminal vertex. A first free frontier at distance n is
strictly before card(S)*p when the phase is included in the state. -/
theorem phased_first_exit_bound [Fintype S] (p : Nat)
    (next : S × Fin p → S × Fin p) (run : Nat → S × Fin p)
    (stop : S × Fin p → Prop) (n : Nat)
    (hstep : ∀ k, run (k+1) = next (run k))
    (hend : stop (run n)) (hfirst : ∀ k, k < n → ¬ stop (run k)) :
    n+1 ≤ Fintype.card S * p := by
  simpa using first_exit_bound next run stop n hstep hend hfirst

/-- If a copy-origin distance is an integral number of primitive periods
inside a first-exit segment, it uses fewer laps than reader states. -/
theorem origin_laps_bound (states p exitDepth laps : Nat)
    (hexit : exitDepth+1 ≤ states*p) (hdistance : laps*p ≤ exitDepth) :
    laps < states := by
  by_contra h
  have hle : states ≤ laps := by omega
  have hm := Nat.mul_le_mul_right p hle
  omega

open PeriodicCopyHeadNormalization BoundedPrefixPeriodicOverlap

/-- Only complete suffixes ending at F are bounded. This is strictly weaker
than CrossBound, which constrains every prefix factor. -/
def SuffixBound (q : Nat → Annotation V H I) (F N K : Nat) : Prop :=
  ∀ s t, s < F → F ≤ t → t+(F-s) ≤ N →
    (∀ d, d < F-s → token q (s+d) = token q (t+d)) → F-s ≤ K

/-- When both ray endpoints have crossed F, a suffix bound suffices:
either the origins are close, or the source origin is near F. No global
prefix-factor bound and no flat-reader assumption is used here. -/
theorem tail_pair_localization (q : Nat → Annotation V H I)
    (F N K a b r : Nat) (ha : a ≤ F)
    (hsa : F ≤ a+r) (hta : a+r ≤ N)
    (hsb : F ≤ b+r) (htb : b+r ≤ N) (hr : Ray q a b r)
    (hc : ∀ d, d < r → (q (a+d)).head = (q (b+d)).head)
    (hsuffix : SuffixBound q F N K) :
    (b ≤ F ∧ Near K a b) ∨ (F < b ∧ F ≤ a+K) := by
  have hm := ray_tokens q a b r hr hc
  by_cases hb : b ≤ F
  · refine Or.inl ⟨hb,?_⟩
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · let s := a+(F-b)
      have hs : s < F := by dsimp [s]; omega
      have hlen : F-s = b-a := by dsimp [s]; omega
      have bound := hsuffix s F hs (by omega) (by rw [hlen]; omega) (by
        intro d hd
        have he := hm (F-b+d) (by rw [hlen] at hd; omega)
        have h₁ : a+(F-b+d) = s+d := by dsimp [s]; omega
        have h₂ : b+(F-b+d) = F+d := by omega
        simpa only [h₁,h₂] using he)
      unfold Near
      rw [hlen] at bound
      omega
    · unfold Near
      omega
    · let s := b+(F-a)
      have hs : s < F := by dsimp [s]; omega
      have hlen : F-s = a-b := by dsimp [s]; omega
      have bound := hsuffix s F hs (by omega) (by rw [hlen]; omega) (by
        intro d hd
        have he := hm (F-a+d) (by rw [hlen] at hd; omega)
        have h₁ : a+(F-a+d) = F+d := by omega
        have h₂ : b+(F-a+d) = s+d := by dsimp [s]; omega
        simpa only [h₁,h₂] using he.symm)
      unfold Near
      rw [hlen] at bound
      omega
  · refine Or.inr ⟨by omega,?_⟩
    by_cases heq : a = F
    · omega
    · have bound := hsuffix a b (by omega) (by omega) (by omega)
        (fun d hd => hm d (by omega))
      omega

end NSSE.PeriodicReaderFirstExit
