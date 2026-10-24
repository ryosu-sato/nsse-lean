import NSSE.RankAvoidanceCompiler
import Mathlib.Data.Fintype.Defs

/-! # Actual finite-model evaluation of the complete rank formula

Relation truth is supplied only for individual base-structure tuples.
All first-order connectives and quantifiers are evaluated by recursion on
the actual formula and the finite domain. No FO or avoidance oracle occurs.
-/

namespace NSSE.FiniteRankDecision

open FirstOrder FirstOrder.Language RankAvoidanceCompiler

universe u v w z
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {D : Type z}
variable [L.Structure D] [Fintype D] [DecidableEq D]

abbrev RelationDecision (L : FirstOrder.Language.{u, v}) (D : Type z) [L.Structure D] :=
  ∀ {n : Nat} (r : L.Relations n) (xs : Fin n → D),
    Decidable (FirstOrder.Language.Structure.RelMap r xs)

def boundedDecision (relDec : RelationDecision L D) :
    {n : Nat} → (φ : L.BoundedFormula P n) → (p : P → D) → (xs : Fin n → D) →
      Decidable (φ.Realize p xs)
  | _, .falsum, _, _ => isFalse id
  | _, .equal t₁ t₂, p, xs =>
      inferInstanceAs (Decidable (t₁.realize (Sum.elim p xs) = t₂.realize (Sum.elim p xs)))
  | _, .rel r ts, p, xs => relDec r (fun i => (ts i).realize (Sum.elim p xs))
  | _, .imp φ ψ, p, xs =>
      letI := boundedDecision relDec φ p xs
      letI := boundedDecision relDec ψ p xs
      inferInstanceAs (Decidable (φ.Realize p xs → ψ.Realize p xs))
  | _, .all φ, p, xs =>
      letI : DecidablePred (fun x : D => φ.Realize p (Fin.snoc xs x)) :=
        fun x => boundedDecision relDec φ p (Fin.snoc xs x)
      inferInstanceAs (Decidable (∀ x : D, φ.Realize p (Fin.snoc xs x)))

def formulaDecision (relDec : RelationDecision L D) (φ : L.Formula P) (p : P → D) :
    Decidable (φ.Realize p) := boundedDecision relDec φ p Fin.elim0

/-- A total finite Boolean evaluator of the actual output formula. -/
def evaluate (relDec : RelationDecision L D) (φ : L.Formula P) (p : P → D) : Bool :=
  @decide (φ.Realize p) (formulaDecision relDec φ p)

theorem evaluate_correct (relDec : RelationDecision L D) (φ : L.Formula P) (p : P → D) :
    evaluate relDec φ p = true ↔ φ.Realize p := by
  letI := formulaDecision relDec φ p
  exact decide_eq_true_iff

def decideAvoidance (h : Nat) (I : Problem) {D : Type*}
    [I.language.Structure D] [Fintype D] [DecidableEq D]
    (relDec : RelationDecision I.language D) (p : I.Parameters → D) : Bool :=
  evaluate relDec (solve h I) p

theorem decideAvoidance_correct (h : Nat) (I : Problem) {D : Type*}
    [I.language.Structure D] [Fintype D] [DecidableEq D]
    (relDec : RelationDecision I.language D) (p : I.Parameters → D)
    (hb : RankBound I p h) :
    decideAvoidance h I relDec p = true ↔ Avoid I p :=
  (evaluate_correct relDec (solve h I) p).trans (solve_correct h I p hb)

theorem decideAvoidance_false_iff (h : Nat) (I : Problem) {D : Type*}
    [I.language.Structure D] [Fintype D] [DecidableEq D]
    (relDec : RelationDecision I.language D) (p : I.Parameters → D)
    (hb : RankBound I p h) :
    decideAvoidance h I relDec p = false ↔ ¬ Avoid I p := by
  have hc := decideAvoidance_correct h I relDec p hb
  constructor
  · intro hf ha
    have ht := hc.mpr ha
    rw [hf] at ht
    cases ht
  · intro hn
    cases hd : decideAvoidance h I relDec p with
    | false => rfl
    | true => exact False.elim (hn (hc.mp hd))

/-- The semantic decision is computed from the Boolean algorithm; the
rank proof certifies its branches and is not inspected during evaluation. -/
def avoidanceDecision (h : Nat) (I : Problem) {D : Type*}
    [I.language.Structure D] [Fintype D] [DecidableEq D]
    (relDec : RelationDecision I.language D) (p : I.Parameters → D)
    (hb : RankBound I p h) : Decidable (Avoid I p) :=
  if he : decideAvoidance h I relDec p = true then
    isTrue ((decideAvoidance_correct h I relDec p hb).mp he)
  else isFalse (fun ha => he ((decideAvoidance_correct h I relDec p hb).mpr ha))

end NSSE.FiniteRankDecision
