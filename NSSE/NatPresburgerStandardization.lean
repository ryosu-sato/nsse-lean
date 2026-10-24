import NSSE.NatPresburgerFiniteEvaluation

/-!
# Standardizing Presburger formulas

The convenience atom `afterCongruent` is recursively lowered to an
existential difference variable, equality, and congruence.  Under the
natural condition `residue < modulus`, this produces an equivalent formula
using only the standard Presburger atoms.
-/

namespace NSSE

namespace NatPresburger

def ResiduesWellFormed : NatPresburger arity → Prop
  | .falsum => True
  | .equal _ _ => True
  | .lessEqual _ _ => True
  | .congruent _ _ _ => True
  | .afterCongruent _ _ modulus residue =>
      residue < modulus
  | .neg formula => formula.ResiduesWellFormed
  | .conj left right =>
      left.ResiduesWellFormed ∧
        right.ResiduesWellFormed
  | .disj left right =>
      left.ResiduesWellFormed ∧
        right.ResiduesWellFormed
  | .existsQ formula => formula.ResiduesWellFormed

def Standard : NatPresburger arity → Prop
  | .falsum => True
  | .equal _ _ => True
  | .lessEqual _ _ => True
  | .congruent _ _ _ => True
  | .afterCongruent _ _ _ _ => False
  | .neg formula => formula.Standard
  | .conj left right =>
      left.Standard ∧ right.Standard
  | .disj left right =>
      left.Standard ∧ right.Standard
  | .existsQ formula => formula.Standard

def lowerAfterCongruentTotal
    (expression : NatLinearExpr arity)
    (threshold modulus residue : Nat) :
    NatPresburger arity :=
  if modulus = 0 then
    .equal expression (.const (threshold + residue))
  else if residue < modulus then
    lowerAfterCongruent expression threshold modulus residue
  else
    .falsum

theorem eval_lowerAfterCongruentTotal_iff
    (expression : NatLinearExpr arity)
    (threshold modulus residue : Nat)
    (valuation : Fin arity → Nat) :
    (lowerAfterCongruentTotal expression threshold
      modulus residue).Eval valuation ↔
      (.afterCongruent expression threshold modulus residue :
        NatPresburger arity).Eval valuation := by
  by_cases hzero : modulus = 0
  · subst modulus
    simp only [lowerAfterCongruentTotal, if_pos,
      Eval, NatLinearExpr.eval_const, Nat.mod_zero]
    omega
  · simp only [lowerAfterCongruentTotal, hzero, if_false]
    by_cases hresidue : residue < modulus
    · rw [if_pos hresidue]
      exact eval_lowerAfterCongruent_iff
        expression threshold modulus residue
          valuation hresidue
    · rw [if_neg hresidue]
      simp only [Eval, false_iff]
      rintro ⟨_, heq⟩
      have hmodulus : 0 < modulus := Nat.pos_of_ne_zero hzero
      have hlt :
          (expression.Eval valuation - threshold) % modulus <
            modulus :=
        Nat.mod_lt _ hmodulus
      omega

def standardize :
    NatPresburger arity → NatPresburger arity
  | .falsum => .falsum
  | .equal left right => .equal left right
  | .lessEqual left right => .lessEqual left right
  | .congruent left right modulus =>
      .congruent left right modulus
  | .afterCongruent expression threshold modulus residue =>
      lowerAfterCongruentTotal
        expression threshold modulus residue
  | .neg formula => .neg formula.standardize
  | .conj left right =>
      .conj left.standardize right.standardize
  | .disj left right =>
      .disj left.standardize right.standardize
  | .existsQ formula => .existsQ formula.standardize

theorem standard_standardize
    (formula : NatPresburger arity) :
    formula.standardize.Standard := by
  induction formula with
  | falsum => trivial
  | equal left right => trivial
  | lessEqual left right => trivial
  | congruent left right modulus => trivial
  | afterCongruent expression threshold modulus residue =>
      simp only [standardize, lowerAfterCongruentTotal]
      split
      · trivial
      · split <;>
          simp [lowerAfterCongruent, Standard]
  | neg formula ih =>
      exact ih
  | conj left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩
  | disj left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩
  | existsQ formula ih =>
      exact ih

theorem residuesWellFormed_standardize
    (formula : NatPresburger arity) :
    formula.standardize.ResiduesWellFormed := by
  induction formula with
  | falsum => trivial
  | equal left right => trivial
  | lessEqual left right => trivial
  | congruent left right modulus => trivial
  | afterCongruent expression threshold modulus residue =>
      simp only [standardize, lowerAfterCongruentTotal]
      split
      · trivial
      · split <;>
          simp [lowerAfterCongruent,
            ResiduesWellFormed]
  | neg formula ih =>
      exact ih
  | conj left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩
  | disj left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight⟩
  | existsQ formula ih =>
      exact ih

theorem standardize_eq_self_of_standard
    (formula : NatPresburger arity)
    (hstandard : formula.Standard) :
    formula.standardize = formula := by
  induction formula with
  | falsum => rfl
  | equal left right => rfl
  | lessEqual left right => rfl
  | congruent left right modulus => rfl
  | afterCongruent expression threshold modulus residue =>
      exact False.elim hstandard
  | neg formula ih =>
      simp only [standardize]
      rw [ih hstandard]
  | conj left right ihLeft ihRight =>
      simp only [standardize]
      rw [ihLeft hstandard.1, ihRight hstandard.2]
  | disj left right ihLeft ihRight =>
      simp only [standardize]
      rw [ihLeft hstandard.1, ihRight hstandard.2]
  | existsQ formula ih =>
      simp only [standardize]
      rw [ih hstandard]

@[simp] theorem standardize_idempotent
    (formula : NatPresburger arity) :
    formula.standardize.standardize =
      formula.standardize :=
  standardize_eq_self_of_standard
    formula.standardize formula.standard_standardize

theorem eval_standardize_iff
    (formula : NatPresburger arity)
    (valuation : Fin arity → Nat) :
    formula.standardize.Eval valuation ↔
      formula.Eval valuation := by
  induction formula with
  | falsum => rfl
  | equal left right => rfl
  | lessEqual left right => rfl
  | congruent left right modulus => rfl
  | afterCongruent expression threshold modulus residue =>
      exact eval_lowerAfterCongruentTotal_iff
        expression threshold modulus residue valuation
  | neg formula ih =>
      exact not_congr (ih valuation)
  | conj left right ihLeft ihRight =>
      exact and_congr
        (ihLeft valuation)
        (ihRight valuation)
  | disj left right ihLeft ihRight =>
      exact or_congr
        (ihLeft valuation)
        (ihRight valuation)
  | existsQ formula ih =>
      simp only [standardize, Eval]
      constructor
      · rintro ⟨bound, heval⟩
        exact ⟨bound,
          (ih
            (extendValuation valuation bound)).mp heval⟩
      · rintro ⟨bound, heval⟩
        exact ⟨bound,
          (ih
            (extendValuation valuation bound)).mpr heval⟩

theorem eval_standardize_closed_iff
    (formula : NatPresburger 0) :
    formula.standardize.Eval Fin.elim0 ↔
      formula.Eval Fin.elim0 :=
  formula.eval_standardize_iff Fin.elim0

end NatPresburger

end NSSE
