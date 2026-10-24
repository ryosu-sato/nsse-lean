import NSSE.StoredRelationalEvaluation
import NSSE.TowerExpression

/-! A fourth-exponential bound for the actual stored formula evaluator.
The interpreter's counted cost is explicit; no arbitrary relation function
is assigned unit cost. This is an operation-count theorem, not machine time. -/
namespace NSSE.StoredEvaluationTower
open StoredRelationalFormula DirectRankStateTower DirectRankFormulaTower

/-- Includes domain enumeration, valuation lookups and relation interpretation. -/
def budget (d m S K c : Nat) := 1+(d+1)^2+
  StoredRelationalEvaluation.weight d m S K d c*(S*(d+1)^S)

theorem budget_mono (d m K c : Nat) {S T : Nat} (h : S ≤ T) :
    budget d m S K c ≤ budget d m T K c := by
  unfold budget StoredRelationalEvaluation.weight
  gcongr; omega

private def coefficient : PolynomialTowerEnvelope.Expr :=
  let t : PolynomialTowerEnvelope.Expr := .var 0
  1+(t+1)^2+3+2*(t+t)+t+3*t+t*(2+t+t)+t

private theorem coefficient_value (t : Nat) :
    PolynomialTowerEnvelope.eval ![t,0,0,0] coefficient =
      1+(t+1)^2+StoredRelationalEvaluation.weight t t t t t t := by
  simp only [coefficient, PolynomialTowerEnvelope.eval, StoredRelationalEvaluation.weight]
  simp only [Matrix.cons_val_zero]
  ring

/-- Only one tower level is added by exhaustive finite evaluation. -/
theorem budget_tower (d m S K c x : Nat) (hS : S ≤ tower 3 x) :
    budget d m S K c ≤ tower 4 (x+d+m+K+c+64) := by
  let y := x+d+m+K+c
  let t := tower 3 y
  have hx : x ≤ y := by dsimp [y]; omega
  have hs : S ≤ t := hS.trans (tower_mono 3 hx)
  have hd : d ≤ t := (show d ≤ y by dsimp [y]; omega).trans
    (TowerExpression.height_mono 0 3 y (by decide))
  have hm : m ≤ t := (show m ≤ y by dsimp [y]; omega).trans
    (TowerExpression.height_mono 0 3 y (by decide))
  have hk : K ≤ t := (show K ≤ y by dsimp [y]; omega).trans
    (TowerExpression.height_mono 0 3 y (by decide))
  have hc : c ≤ t := (show c ≤ y by dsimp [y]; omega).trans
    (TowerExpression.height_mono 0 3 y (by decide))
  have hp : 1+(d+1)^2+StoredRelationalEvaluation.weight d m S K d c ≤
      1+(t+1)^2+StoredRelationalEvaluation.weight t t t t t t := by
    unfold StoredRelationalEvaluation.weight
    gcongr
  have he := envelope_three coefficient ![t,0,0,0] y (by
    intro i; fin_cases i
    · exact le_rfl
    all_goals exact Nat.zero_le _)
  rw [coefficient_value] at he
  have hw : PolynomialTowerEnvelope.weight coefficient ≤ 60 := by decide
  have hcoeff := (hp.trans he).trans (tower_mono 3 (Nat.add_le_add_left hw y))
  have hcoeff4 := hcoeff.trans (TowerExpression.height_mono 3 4 (y+60) (by decide))
  have hv := CountedRankEvaluationTower.visits_tower hS d
  have hv' : S*(d+1)^S ≤ tower 4 (y+60) := hv.trans (tower_mono 4 (by dsimp [y]; omega))
  have hprod := Nat.mul_le_mul (show StoredRelationalEvaluation.weight d m S K d c ≤ tower 4 (y+60) by omega) hv'
  have hsq := TowerExpression.square_step 4 (y+60) (by decide)
  have hdbl := TowerExpression.double_step 3 (y+60+1)
  have hsmall : tower 4 (y+60) ≤ tower 4 (y+60+1) := tower_mono 4 (by omega)
  have hlast : tower 4 (y+60+1+1) ≤ tower 4 (x+d+m+K+c+64) := tower_mono 4 (by dsimp [y]; omega)
  unfold budget
  nlinarith

/-- Applies to the executable evaluator, with its actual interpreter bound. -/
theorem decide_tower {R : Nat → Type} {d m : Nat}
    (rel : StoredRelationalEvaluation.Interpreter R d)
    (φ : Data R (Fin m) 0) (ps : FiniteValuationLookup.Values d m)
    (K c x : Nat) (hr : ∀ k, k ≤ K → ∀ r xs, (rel k r xs).2 ≤ c)
    (hk : arity φ ≤ K) (hs : nodes φ ≤ tower 3 x) :
    (StoredRelationalEvaluation.decideFormula rel φ ps).2 ≤ tower 4 (x+d+m+K+c+64) :=
  (StoredRelationalEvaluation.decide_bound rel φ ps K c hr hk).trans
    (budget_tower d m (nodes φ) K c x hs)

/-- Adapter construction, rank compilation, closure and renaming, and unary
lookup evaluation. The adapter cost is retained as a separate summand. -/
def totalBudget (d adapter compile S : Nat) :=
  5+adapter+compile+28*S+budget d 0 S 2 (d+3)

private def overhead : PolynomialTowerEnvelope.Expr :=
  5 + .var 0 + .var 1 + 28 * .var 2

theorem totalBudget_tower (d adapter compile S x : Nat)
    (ha : adapter ≤ tower 3 x) (hc : compile ≤ tower 3 x) (hs : S ≤ tower 3 x) :
    totalBudget d adapter compile S ≤ tower 4 (x+2*d+70) := by
  have he := envelope_three overhead ![adapter,compile,S,0] x (by
    intro i; fin_cases i
    · exact ha
    · exact hc
    · exact hs
    · exact Nat.zero_le _)
  have hw : PolynomialTowerEnvelope.weight overhead ≤ 50 := by decide
  have hev : PolynomialTowerEnvelope.eval ![adapter,compile,S,0] overhead =
      5+adapter+compile+28*S := rfl
  rw [hev] at he
  have hh := (he.trans (tower_mono 3 (Nat.add_le_add_left hw x))).trans
    (TowerExpression.height_mono 3 4 (x+50) (by decide))
  have hh' := hh.trans (tower_mono 4 (show x+50 ≤ x+2*d+69 by omega))
  have hb := budget_tower d 0 S 2 (d+3) x hs
  have hb' : budget d 0 S 2 (d+3) ≤ tower 4 (x+2*d+69) := by
    have heq : x+d+0+2+(d+3)+64 = x+2*d+69 := by omega
    rw [heq] at hb
    exact hb
  have hd := TowerExpression.double_step 3 (x+2*d+69)
  change 2*tower 4 (x+2*d+69) ≤ tower 4 (x+2*d+69+1) at hd
  unfold totalBudget
  have heq : x+2*d+69+1 = x+2*d+70 := by omega
  rw [heq] at hd
  omega

end NSSE.StoredEvaluationTower
