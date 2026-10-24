import NSSE.DFAOrbitPeriodicity

/-!
# A small executable fragment of unary Presburger arithmetic

Theorem A ultimately needs multivariable Presburger formulas.  This file
starts with the exact unary fragment required by Lemma A.0: finite points,
Boolean operations, lower bounds, and congruences after a threshold.
-/

namespace NSSE

inductive UnaryPresburger where
  | falsum
  | equal (value : Nat)
  | afterCongruent (threshold modulus residue : Nat)
  | disj (left right : UnaryPresburger)

namespace UnaryPresburger

def Eval : UnaryPresburger → Nat → Prop
  | .falsum, _ => False
  | .equal value, n => n = value
  | .afterCongruent threshold modulus residue, n =>
      threshold ≤ n ∧ (n - threshold) % modulus = residue
  | .disj left right, n => left.Eval n ∨ right.Eval n

def disjoin : List UnaryPresburger → UnaryPresburger
  | [] => .falsum
  | formula :: formulas => .disj formula (disjoin formulas)

theorem eval_disjoin_iff
    (formulas : List UnaryPresburger) (n : Nat) :
    (disjoin formulas).Eval n ↔
      ∃ formula ∈ formulas, formula.Eval n := by
  induction formulas with
  | nil => simp [disjoin, Eval]
  | cons formula formulas ih =>
      simp [disjoin, Eval, ih]

noncomputable def eventuallyPeriodicFormula
    (P : Nat → Prop) (threshold period : Nat) :
    UnaryPresburger := by
  classical
  exact
    let initial :=
      (List.range threshold).filter
        (fun n => decide (P n)) |>.map .equal
    let residues :=
      (List.range period).filter
        (fun r => decide (P (threshold + r))) |>.map
          (.afterCongruent threshold period)
    .disj (disjoin initial) (disjoin residues)

/-- Every eventually periodic unary predicate is represented by a finite
Boolean combination of equality, order, and congruence atoms. -/
theorem eventuallyPeriodicFormula_correct
    (P : Nat → Prop) (threshold period : Nat)
    (hperiodPos : 0 < period)
    (hperiod :
      ∀ t, P (threshold + t + period) ↔
        P (threshold + t))
    (n : Nat) :
    (eventuallyPeriodicFormula P threshold period).Eval n ↔ P n := by
  classical
  unfold eventuallyPeriodicFormula
  simp only [Eval, eval_disjoin_iff]
  by_cases hn : n < threshold
  · constructor
    · rintro (⟨formula, hformula, heval⟩ |
          ⟨formula, hformula, heval⟩)
      · simp only [List.mem_map, List.mem_filter,
          List.mem_range] at hformula
        obtain ⟨k, ⟨hkRange, hkP⟩, rfl⟩ := hformula
        have hkProp : P k := of_decide_eq_true hkP
        simpa [Eval] using heval ▸ hkProp
      · simp only [List.mem_map, List.mem_filter,
          List.mem_range] at hformula
        obtain ⟨r, ⟨hrRange, hrP⟩, rfl⟩ := hformula
        exact False.elim (by
          simpa [Eval] using heval |>.1.not_lt hn)
    · intro hnP
      left
      refine ⟨.equal n, ?_, ?_⟩
      · simp [hn, hnP]
      · simp [Eval]
  · have hthreshold : threshold ≤ n := by omega
    have hcanonical :=
      eventuallyPeriodic_iff_canonicalResidue
        P hperiod hthreshold
    constructor
    · rintro (⟨formula, hformula, heval⟩ |
          ⟨formula, hformula, heval⟩)
      · simp only [List.mem_map, List.mem_filter,
          List.mem_range] at hformula
        obtain ⟨k, ⟨hkRange, hkP⟩, rfl⟩ := hformula
        have := heval
        simp [Eval] at this
        omega
      · simp only [List.mem_map, List.mem_filter,
          List.mem_range] at hformula
        obtain ⟨r, ⟨hrRange, hrP⟩, rfl⟩ := hformula
        have hrProp : P (threshold + r) :=
          of_decide_eq_true hrP
        have heq :
            (n - threshold) % period = r := by
          exact heval.2
        apply hcanonical.2
        rw [heq]
        exact hrProp
    · intro hnP
      right
      let r := (n - threshold) % period
      have hrRange : r < period :=
        Nat.mod_lt _ hperiodPos
      have hrP : P (threshold + r) :=
        hcanonical.1 hnP
      refine ⟨.afterCongruent threshold period r,
        ?_, ?_⟩
      · simp [r, hrRange, hrP]
      · exact ⟨hthreshold, rfl⟩

end UnaryPresburger

namespace DFA

/-- Lemma A.0 with an explicit finite Presburger formula for acceptance
along `u^n`. -/
theorem accepts_word_powers_presburger
    (A : DFA α Q) [Fintype Q] (u : Word α) :
    ∃ formula : UnaryPresburger,
      ∀ n, formula.Eval n ↔
        A.Accepts (Word.power u n) := by
  obtain ⟨threshold, period, _hthreshold,
      hperiodPos, _hperiodBound, hperiod⟩ :=
    A.accepts_word_powers_eventually_periodic u
  refine ⟨UnaryPresburger.eventuallyPeriodicFormula
      (fun n => A.Accepts (Word.power u n))
      threshold period, ?_⟩
  intro n
  exact UnaryPresburger.eventuallyPeriodicFormula_correct
    (fun k => A.Accepts (Word.power u k))
    threshold period hperiodPos hperiod n

end DFA

/-- Equality to a fixed target along any finite functional orbit has an
explicit unary Presburger formula. -/
theorem finite_orbit_eq_presburger
    (f : Q → Q) [Fintype Q] (start target : Q) :
    ∃ formula : UnaryPresburger,
      ∀ n, formula.Eval n ↔
        (f^[n]) start = target := by
  obtain ⟨threshold, period, _hthreshold,
      hperiodPos, _hperiodBound, hperiod⟩ :=
    finite_orbit_eventually_periodic f start
  refine ⟨UnaryPresburger.eventuallyPeriodicFormula
      (fun n => (f^[n]) start = target)
      threshold period, ?_⟩
  intro n
  exact UnaryPresburger.eventuallyPeriodicFormula_correct
    (fun k => (f^[k]) start = target)
    threshold period hperiodPos
    (fun t => by
      change ((f^[threshold + t + period]) start = target ↔
        (f^[threshold + t]) start = target)
      rw [hperiod t]) n

end NSSE
