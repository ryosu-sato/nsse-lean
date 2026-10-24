import NSSE.GeneralEmptyPumpNormalizationStructure

/-!
# Executable finite-domain evaluation of Presburger formulas

This module gives every `NatPresburger` formula an executable semantics in
which each existential quantifier ranges over `0, ..., bound - 1`.  The
Boolean evaluator is proved exact for that finite-domain semantics.  For
quantifier-free formulas it agrees with the ordinary unbounded semantics
for every bound.
-/

namespace NSSE

namespace NatPresburger

def FiniteEval :
    NatPresburger arity →
      (Fin arity → Nat) → Nat → Prop
  | .falsum, _, _ => False
  | .equal left right, valuation, _ =>
      left.Eval valuation = right.Eval valuation
  | .lessEqual left right, valuation, _ =>
      left.Eval valuation ≤ right.Eval valuation
  | .congruent left right modulus, valuation, _ =>
      left.Eval valuation % modulus =
        right.Eval valuation % modulus
  | .afterCongruent expression threshold modulus residue,
      valuation, _ =>
      threshold ≤ expression.Eval valuation ∧
        (expression.Eval valuation - threshold) % modulus =
          residue
  | .neg formula, valuation, bound =>
      ¬formula.FiniteEval valuation bound
  | .conj left right, valuation, bound =>
      left.FiniteEval valuation bound ∧
        right.FiniteEval valuation bound
  | .disj left right, valuation, bound =>
      left.FiniteEval valuation bound ∨
        right.FiniteEval valuation bound
  | .existsQ formula, valuation, bound =>
      ∃ value < bound,
        formula.FiniteEval
          (extendValuation valuation value) bound

def evalFinite :
    NatPresburger arity →
      (Fin arity → Nat) → Nat → Bool
  | .falsum, _, _ => false
  | .equal left right, valuation, _ =>
      decide (left.Eval valuation = right.Eval valuation)
  | .lessEqual left right, valuation, _ =>
      decide (left.Eval valuation ≤ right.Eval valuation)
  | .congruent left right modulus, valuation, _ =>
      decide
        (left.Eval valuation % modulus =
          right.Eval valuation % modulus)
  | .afterCongruent expression threshold modulus residue,
      valuation, _ =>
      decide
        (threshold ≤ expression.Eval valuation ∧
          (expression.Eval valuation - threshold) % modulus =
            residue)
  | .neg formula, valuation, bound =>
      !(formula.evalFinite valuation bound)
  | .conj left right, valuation, bound =>
      left.evalFinite valuation bound &&
        right.evalFinite valuation bound
  | .disj left right, valuation, bound =>
      left.evalFinite valuation bound ||
        right.evalFinite valuation bound
  | .existsQ formula, valuation, bound =>
      (List.range bound).any fun value =>
        formula.evalFinite
          (extendValuation valuation value) bound

theorem evalFinite_eq_true_iff
    (formula : NatPresburger arity)
    (valuation : Fin arity → Nat)
    (bound : Nat) :
    formula.evalFinite valuation bound = true ↔
      formula.FiniteEval valuation bound := by
  induction formula with
  | falsum =>
      simp [evalFinite, FiniteEval]
  | equal left right =>
      simp [evalFinite, FiniteEval]
  | lessEqual left right =>
      simp [evalFinite, FiniteEval]
  | congruent left right modulus =>
      simp [evalFinite, FiniteEval]
  | afterCongruent expression threshold modulus residue =>
      simp [evalFinite, FiniteEval]
  | neg formula ih =>
      cases hvalue :
          formula.evalFinite valuation bound with
      | false =>
          simp only [evalFinite, hvalue,
            Bool.not_false, FiniteEval]
          constructor
          · intro _ heval
            have htrue :=
              (ih valuation).mpr heval
            rw [hvalue] at htrue
            contradiction
          · intro _
            trivial
      | true =>
          simp [evalFinite, hvalue, FiniteEval,
            (ih valuation).mp hvalue]
  | conj left right ihLeft ihRight =>
      simp [evalFinite, FiniteEval, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [evalFinite, FiniteEval, ihLeft, ihRight]
  | existsQ formula ih =>
      simp [evalFinite, FiniteEval, ih]

def ValuationBelow
    (valuation : Fin arity → Nat)
    (bound : Nat) : Prop :=
  ∀ index, valuation index < bound

theorem valuationBelow_extendValuation_iff
    (valuation : Fin arity → Nat)
    (value bound : Nat) :
    ValuationBelow
        (extendValuation valuation value) bound ↔
      ValuationBelow valuation bound ∧ value < bound := by
  constructor
  · intro hbelow
    constructor
    · intro index
      simpa using hbelow index.castSucc
    · simpa using hbelow (Fin.last arity)
  · rintro ⟨hvaluation, hvalue⟩ index
    refine Fin.lastCases ?_ (fun earlier => ?_) index
    · simpa
    · simpa using hvaluation earlier

theorem finiteEval_existentialClosure_iff
    (formula : NatPresburger arity)
    (bound : Nat) :
    (existentialClosure arity formula).FiniteEval
        Fin.elim0 bound ↔
      ∃ valuation : Fin arity → Nat,
        ValuationBelow valuation bound ∧
          formula.FiniteEval valuation bound := by
  induction arity with
  | zero =>
      simp only [existentialClosure]
      constructor
      · intro heval
        exact ⟨Fin.elim0,
          fun index => Fin.elim0 index, heval⟩
      · rintro ⟨valuation, _, heval⟩
        have hvaluation : valuation = Fin.elim0 := by
          funext index
          exact Fin.elim0 index
        simpa [hvaluation] using heval
  | succ arity ih =>
      rw [existentialClosure, ih]
      simp only [FiniteEval]
      constructor
      · rintro ⟨valuation, hbelow,
          value, hvalue, heval⟩
        exact ⟨extendValuation valuation value,
          (valuationBelow_extendValuation_iff
            valuation value bound).mpr
              ⟨hbelow, hvalue⟩,
          heval⟩
      · rintro ⟨valuation, hbelow, heval⟩
        let prefixValuation : Fin arity → Nat :=
          fun index => valuation index.castSucc
        let value : Nat := valuation (Fin.last arity)
        have heta :
            extendValuation prefixValuation value =
              valuation := by
          funext index
          refine Fin.lastCases ?_ (fun earlier => ?_) index
          · simp [extendValuation, value]
          · simp [extendValuation, prefixValuation]
        have hprefix :
            ValuationBelow prefixValuation bound := by
          intro index
          exact hbelow index.castSucc
        have hvalue : value < bound :=
          hbelow (Fin.last arity)
        exact ⟨prefixValuation, hprefix, value,
          hvalue, by simpa [heta] using heval⟩

theorem evalFinite_existentialClosure_eq_true_iff
    (formula : NatPresburger arity)
    (bound : Nat) :
    (existentialClosure arity formula).evalFinite
        Fin.elim0 bound = true ↔
      ∃ valuation : Fin arity → Nat,
        ValuationBelow valuation bound ∧
          formula.FiniteEval valuation bound := by
  rw [evalFinite_eq_true_iff,
    finiteEval_existentialClosure_iff]

theorem finiteEval_universalClosure_iff
    (formula : NatPresburger arity)
    (bound : Nat) :
    (universalClosure arity formula).FiniteEval
        Fin.elim0 bound ↔
      ∀ valuation : Fin arity → Nat,
        ValuationBelow valuation bound →
          formula.FiniteEval valuation bound := by
  rw [universalClosure]
  simp only [FiniteEval,
    finiteEval_existentialClosure_iff]
  push_neg
  rfl

theorem evalFinite_universalClosure_eq_true_iff
    (formula : NatPresburger arity)
    (bound : Nat) :
    (universalClosure arity formula).evalFinite
        Fin.elim0 bound = true ↔
      ∀ valuation : Fin arity → Nat,
        ValuationBelow valuation bound →
          formula.FiniteEval valuation bound := by
  rw [evalFinite_eq_true_iff,
    finiteEval_universalClosure_iff]

def QuantifierFree : NatPresburger arity → Prop
  | .falsum => True
  | .equal _ _ => True
  | .lessEqual _ _ => True
  | .congruent _ _ _ => True
  | .afterCongruent _ _ _ _ => True
  | .neg formula => formula.QuantifierFree
  | .conj left right =>
      left.QuantifierFree ∧ right.QuantifierFree
  | .disj left right =>
      left.QuantifierFree ∧ right.QuantifierFree
  | .existsQ _ => False

theorem finiteEval_iff_eval_of_quantifierFree
    (formula : NatPresburger arity)
    (hfree : formula.QuantifierFree)
    (valuation : Fin arity → Nat)
    (bound : Nat) :
    formula.FiniteEval valuation bound ↔
      formula.Eval valuation := by
  induction formula with
  | falsum => rfl
  | equal left right => rfl
  | lessEqual left right => rfl
  | congruent left right modulus => rfl
  | afterCongruent expression threshold modulus residue =>
      rfl
  | neg formula ih =>
      exact not_congr (ih hfree valuation)
  | conj left right ihLeft ihRight =>
      exact and_congr
        (ihLeft hfree.1 valuation)
        (ihRight hfree.2 valuation)
  | disj left right ihLeft ihRight =>
      exact or_congr
        (ihLeft hfree.1 valuation)
        (ihRight hfree.2 valuation)
  | existsQ formula =>
      exact False.elim hfree

theorem evalFinite_eq_true_iff_eval_of_quantifierFree
    (formula : NatPresburger arity)
    (hfree : formula.QuantifierFree)
    (valuation : Fin arity → Nat)
    (bound : Nat) :
    formula.evalFinite valuation bound = true ↔
      formula.Eval valuation := by
  rw [formula.evalFinite_eq_true_iff,
    formula.finiteEval_iff_eval_of_quantifierFree
      hfree]

theorem evalFinite_existentialClosure_eq_true_iff_eval
    (formula : NatPresburger arity)
    (hfree : formula.QuantifierFree)
    (bound : Nat) :
    (existentialClosure arity formula).evalFinite
        Fin.elim0 bound = true ↔
      ∃ valuation : Fin arity → Nat,
        ValuationBelow valuation bound ∧
          formula.Eval valuation := by
  rw [evalFinite_existentialClosure_eq_true_iff]
  constructor
  · rintro ⟨valuation, hbelow, heval⟩
    exact ⟨valuation, hbelow,
      (formula.finiteEval_iff_eval_of_quantifierFree
        hfree valuation bound).mp heval⟩
  · rintro ⟨valuation, hbelow, heval⟩
    exact ⟨valuation, hbelow,
      (formula.finiteEval_iff_eval_of_quantifierFree
        hfree valuation bound).mpr heval⟩

theorem evalFinite_universalClosure_eq_true_iff_eval
    (formula : NatPresburger arity)
    (hfree : formula.QuantifierFree)
    (bound : Nat) :
    (universalClosure arity formula).evalFinite
        Fin.elim0 bound = true ↔
      ∀ valuation : Fin arity → Nat,
        ValuationBelow valuation bound →
          formula.Eval valuation := by
  rw [evalFinite_universalClosure_eq_true_iff]
  constructor
  · intro h valuation hbelow
    exact (formula.finiteEval_iff_eval_of_quantifierFree
      hfree valuation bound).mp
        (h valuation hbelow)
  · intro h valuation hbelow
    exact (formula.finiteEval_iff_eval_of_quantifierFree
      hfree valuation bound).mpr
        (h valuation hbelow)

def evalFiniteClosed
    (formula : NatPresburger 0)
    (bound : Nat) : Bool :=
  formula.evalFinite Fin.elim0 bound

theorem evalFiniteClosed_eq_true_iff
    (formula : NatPresburger 0)
    (bound : Nat) :
    formula.evalFiniteClosed bound = true ↔
      formula.FiniteEval Fin.elim0 bound :=
  formula.evalFinite_eq_true_iff Fin.elim0 bound

end NatPresburger

end NSSE
