import NSSE.NatPresburgerVacuousQuantifier

/-!
# Eliminating quantifiers over constant finite intervals

An existential quantifier over a fixed closed interval is expanded into a
finite disjunction after substituting every numeral for the last variable.
The universal dual is expanded into a finite conjunction.
-/

namespace NSSE

namespace NatPresburger

def finiteDisjoin :
    List (NatPresburger arity) → NatPresburger arity
  | [] => .falsum
  | formula :: formulas =>
      .disj formula (finiteDisjoin formulas)

theorem eval_finiteDisjoin_iff
    (formulas : List (NatPresburger arity))
    (valuation : Fin arity → Nat) :
    (finiteDisjoin formulas).Eval valuation ↔
      ∃ formula ∈ formulas, formula.Eval valuation := by
  induction formulas with
  | nil => simp [finiteDisjoin, Eval]
  | cons formula formulas ih =>
      simp [finiteDisjoin, Eval, ih]

def finiteConjoin :
    List (NatPresburger arity) → NatPresburger arity
  | [] => .neg .falsum
  | formula :: formulas =>
      .conj formula (finiteConjoin formulas)

theorem eval_finiteConjoin_iff
    (formulas : List (NatPresburger arity))
    (valuation : Fin arity → Nat) :
    (finiteConjoin formulas).Eval valuation ↔
      ∀ formula ∈ formulas, formula.Eval valuation := by
  induction formulas with
  | nil => simp [finiteConjoin, Eval]
  | cons formula formulas ih =>
      simp [finiteConjoin, Eval, ih]

theorem standard_finiteDisjoin
    (formulas : List (NatPresburger arity))
    (hstandard :
      ∀ formula ∈ formulas, formula.Standard) :
    (finiteDisjoin formulas).Standard := by
  induction formulas with
  | nil => trivial
  | cons formula formulas ih =>
      exact ⟨hstandard formula (by simp),
        ih (fun member hmember =>
          hstandard member (by simp [hmember]))⟩

theorem standard_finiteConjoin
    (formulas : List (NatPresburger arity))
    (hstandard :
      ∀ formula ∈ formulas, formula.Standard) :
    (finiteConjoin formulas).Standard := by
  induction formulas with
  | nil => trivial
  | cons formula formulas ih =>
      exact ⟨hstandard formula (by simp),
        ih (fun member hmember =>
          hstandard member (by simp [hmember]))⟩

theorem quantifierFree_finiteDisjoin
    (formulas : List (NatPresburger arity))
    (hfree :
      ∀ formula ∈ formulas, formula.QuantifierFree) :
    (finiteDisjoin formulas).QuantifierFree := by
  induction formulas with
  | nil => trivial
  | cons formula formulas ih =>
      exact ⟨hfree formula (by simp),
        ih (fun member hmember =>
          hfree member (by simp [hmember]))⟩

theorem quantifierFree_finiteConjoin
    (formulas : List (NatPresburger arity))
    (hfree :
      ∀ formula ∈ formulas, formula.QuantifierFree) :
    (finiteConjoin formulas).QuantifierFree := by
  induction formulas with
  | nil => trivial
  | cons formula formulas ih =>
      exact ⟨hfree formula (by simp),
        ih (fun member hmember =>
          hfree member (by simp [hmember]))⟩

def closedIntervalValues
    (lower upper : Nat) : List Nat :=
  (List.range (upper + 1)).filter
    (fun value => decide (lower ≤ value))

theorem mem_closedIntervalValues_iff
    (lower upper value : Nat) :
    value ∈ closedIntervalValues lower upper ↔
      lower ≤ value ∧ value ≤ upper := by
  simp [closedIntervalValues]
  omega

def eliminateExistsInClosedInterval
    (body : NatPresburger (arity + 1))
    (lower upper : Nat) :
    NatPresburger arity :=
  finiteDisjoin <|
    (closedIntervalValues lower upper).map fun value =>
      body.eliminateDefinedLast (.const value)

theorem eval_eliminateExistsInClosedInterval_iff
    (body : NatPresburger (arity + 1))
    (lower upper : Nat)
    (valuation : Fin arity → Nat) :
    (body.eliminateExistsInClosedInterval
      lower upper).Eval valuation ↔
      ∃ value,
        lower ≤ value ∧ value ≤ upper ∧
          body.Eval
            (extendValuation valuation value) := by
  rw [eliminateExistsInClosedInterval,
    eval_finiteDisjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    rw [List.mem_map] at hformula
    obtain ⟨value, hvalue, rfl⟩ := hformula
    refine ⟨value,
      (mem_closedIntervalValues_iff
        lower upper value).mp hvalue |>.1,
      (mem_closedIntervalValues_iff
        lower upper value).mp hvalue |>.2, ?_⟩
    simpa using
      (body.eval_eliminateDefinedLast_iff
        (.const value) valuation).mp heval
  · rintro ⟨value, hlower, hupper, heval⟩
    refine ⟨body.eliminateDefinedLast (.const value),
      List.mem_map.mpr ⟨value,
        (mem_closedIntervalValues_iff
          lower upper value).mpr ⟨hlower, hupper⟩,
        rfl⟩, ?_⟩
    exact (body.eval_eliminateDefinedLast_iff
      (.const value) valuation).mpr (by simpa using heval)

theorem eval_eliminateExistsInClosedInterval_iff_boundedExists
    (body : NatPresburger (arity + 1))
    (lower upper : Nat)
    (valuation : Fin arity → Nat) :
    (body.eliminateExistsInClosedInterval
        lower upper).Eval valuation ↔
      (boundedExists (.const lower) (.const upper)
        body).Eval valuation := by
  rw [eval_eliminateExistsInClosedInterval_iff,
    eval_boundedExists_iff]
  simp

theorem standard_eliminateExistsInClosedInterval
    (body : NatPresburger (arity + 1))
    (hstandard : body.Standard)
    (lower upper : Nat) :
    (body.eliminateExistsInClosedInterval
      lower upper).Standard := by
  apply standard_finiteDisjoin
  intro formula hformula
  rw [List.mem_map] at hformula
  obtain ⟨value, _, rfl⟩ := hformula
  exact body.standard_eliminateDefinedLast
    hstandard (.const value)

theorem quantifierFree_eliminateExistsInClosedInterval
    (body : NatPresburger (arity + 1))
    (hfree : body.QuantifierFree)
    (lower upper : Nat) :
    (body.eliminateExistsInClosedInterval
      lower upper).QuantifierFree := by
  apply quantifierFree_finiteDisjoin
  intro formula hformula
  rw [List.mem_map] at hformula
  obtain ⟨value, _, rfl⟩ := hformula
  exact body.quantifierFree_substitute hfree
    (substituteLast (.const value))

def eliminateForallInClosedInterval
    (body : NatPresburger (arity + 1))
    (lower upper : Nat) :
    NatPresburger arity :=
  finiteConjoin <|
    (closedIntervalValues lower upper).map fun value =>
      body.eliminateDefinedLast (.const value)

theorem eval_eliminateForallInClosedInterval_iff
    (body : NatPresburger (arity + 1))
    (lower upper : Nat)
    (valuation : Fin arity → Nat) :
    (body.eliminateForallInClosedInterval
      lower upper).Eval valuation ↔
      ∀ value,
        lower ≤ value → value ≤ upper →
          body.Eval
            (extendValuation valuation value) := by
  rw [eliminateForallInClosedInterval,
    eval_finiteConjoin_iff]
  constructor
  · intro hall value hlower hupper
    have hmem :
        value ∈ closedIntervalValues lower upper :=
      (mem_closedIntervalValues_iff
        lower upper value).mpr ⟨hlower, hupper⟩
    have heval := hall
      (body.eliminateDefinedLast (.const value))
      (List.mem_map.mpr ⟨value, hmem, rfl⟩)
    simpa using
      (body.eval_eliminateDefinedLast_iff
        (.const value) valuation).mp heval
  · intro hall formula hformula
    rw [List.mem_map] at hformula
    obtain ⟨value, hvalue, rfl⟩ := hformula
    have hbounds :=
      (mem_closedIntervalValues_iff
        lower upper value).mp hvalue
    exact (body.eval_eliminateDefinedLast_iff
      (.const value) valuation).mpr
        (by simpa using hall value hbounds.1 hbounds.2)

theorem eval_eliminateForallInClosedInterval_iff_boundedForall
    (body : NatPresburger (arity + 1))
    (lower upper : Nat)
    (valuation : Fin arity → Nat) :
    (body.eliminateForallInClosedInterval
        lower upper).Eval valuation ↔
      (boundedForall (.const lower) (.const upper)
        body).Eval valuation := by
  rw [eval_eliminateForallInClosedInterval_iff,
    eval_boundedForall_iff]
  simp

theorem standard_eliminateForallInClosedInterval
    (body : NatPresburger (arity + 1))
    (hstandard : body.Standard)
    (lower upper : Nat) :
    (body.eliminateForallInClosedInterval
      lower upper).Standard := by
  apply standard_finiteConjoin
  intro formula hformula
  rw [List.mem_map] at hformula
  obtain ⟨value, _, rfl⟩ := hformula
  exact body.standard_eliminateDefinedLast
    hstandard (.const value)

theorem quantifierFree_eliminateForallInClosedInterval
    (body : NatPresburger (arity + 1))
    (hfree : body.QuantifierFree)
    (lower upper : Nat) :
    (body.eliminateForallInClosedInterval
      lower upper).QuantifierFree := by
  apply quantifierFree_finiteConjoin
  intro formula hformula
  rw [List.mem_map] at hformula
  obtain ⟨value, _, rfl⟩ := hformula
  exact body.quantifierFree_substitute hfree
    (substituteLast (.const value))

end NatPresburger

end NSSE
