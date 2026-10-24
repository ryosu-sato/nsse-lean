import NSSE.DirectRankPresentationTower

/-! # Standard triple-exponential size bound for the actual rank compiler -/

namespace NSSE.DirectRankFormulaTower

open RankAvoidanceCompiler (Problem)
open DirectRankStateTower PolynomialTowerEnvelope

/-- Adding a natural to the exponent cannot require another tower level. -/
theorem exp_add_le (x n : Nat) : 2^x+n ≤ 2^(x+n) := by
  have hx : 1 ≤ 2^x := Nat.one_le_pow _ _ (by decide)
  have hn : n+1 ≤ 2^n := n.lt_two_pow_self
  rw [pow_add]
  nlinarith

theorem tower_mono (k : Nat) {x y : Nat} (h : x ≤ y) : tower k x ≤ tower k y := by
  induction k with
  | zero => exact h
  | succ k ih => exact exp_mono ih

theorem envelope_three (e : Expr) (v : Fin 4 → Nat) (x : Nat) (hv : ∀ i, v i ≤ tower 3 x) :
    eval v e ≤ tower 3 (x+weight e) := by
  have h := eval_tower e v (2^x) hv
  exact h.trans (tower_mono 2 (exp_add_le x (weight e)))

def exponentExpression : Expr :=
  let B : Expr := .var 0
  max (1+(B+1)*(2*B^6+8*B^8)) (2*B)

def baseExpression : Expr :=
  let B : Expr := .var 0
  let E : Expr := .var 1
  let T : Expr := .var 2
  let g := 40+6*(B+3)+B*(4+B*(24+4*(B+3)))
  let N := 2*B*B
  let G := 109+5*g
  let table := 19+N*(14+2*G)+1*(8+N*(16+2*N*(9+G)))+N*(9+G)+5*((1+1)*N)
  let atom := 5+24*1+(3+B*(8+2*B))+(B+2)+table
  let coeff := 4*(atom+24)*E
  let seed := 1+B*(4+B*(18+3*B))
  let factor := 32+seed+coeff
  let nonempty := 1+B*(4+B*(13+2*B+(B+23)*T))
  (factor+1)*(nonempty+1)

theorem eval_exponent (B : Nat) : eval ![B,0,0,0] exponentExpression =
    max (WholeScalarLoweringBound.presentationExponent B) (2*B) := rfl

theorem eval_base (B : Nat) :
    eval ![B,2^WholeScalarLoweringBound.presentationExponent B,3^B,0] baseExpression =
      DirectRankFormulaClosedBound.base B := rfl

theorem base_tower {B x : Nat} (hb : B ≤ tower 2 x) :
    DirectRankFormulaClosedBound.base B ≤ tower 3 (x+weight exponentExpression+weight baseExpression) := by
  have he := eval_tower exponentExpression ![B,0,0,0] x (by
    intro i; fin_cases i
    · exact hb
    all_goals exact Nat.zero_le _)
  rw [eval_exponent] at he
  have hexp : 2^WholeScalarLoweringBound.presentationExponent B ≤ tower 3 (x+weight exponentExpression) :=
    exp_mono ((le_max_left _ _).trans he)
  have hthree : 3^B ≤ tower 3 (x+weight exponentExpression) := by
    have hp : 3^B ≤ 2^(2*B) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) B
    exact hp.trans (exp_mono ((le_max_right _ _).trans he))
  rw [← eval_base]
  apply envelope_three
  intro i
  fin_cases i
  · exact hb.trans ((self_le_exp _).trans (tower_mono 3 (Nat.le_add_right _ _)))
  · exact hexp
  · exact hthree
  · exact Nat.zero_le _

theorem power_three {a x : Nat} (ha : a ≤ tower 3 x) (h : Nat) : a^(4^h) ≤ tower 3 (x+2*h) := by
  have hp := pow_exp ha (4^h)
  have hf : 4^h = 2^(2*h) := by rw [pow_mul]; rfl
  rw [hf] at hp
  have hm : tower 2 x*2^(2*h) ≤ tower 2 (x+2*h) := by
    change 2^(2^x)*2^(2*h) ≤ 2^(2^(x+2*h))
    rw [← pow_add]
    exact exp_mono (exp_add_le x (2*h))
  simpa only [hf] using hp.trans (exp_mono hm)

def polynomial (S h : Nat) := DirectRankPresentationTower.polynomial S (h+1)+
  weight exponentExpression+weight baseExpression+2*(h+1)

theorem solve_tower (h : Nat) (I : Problem)
    (hr : ∀ i, ArrayAtomExistentialPackages.RowQF (I.rows i)) (hc : ArrayAtomExistentialPackages.RowQF I.candidate) :
    ExactReachabilitySize.nodes (DirectExistentialRankCompiler.solve h I hr hc).toFormula+1 ≤
      tower 3 (polynomial (DirectRankHorizonStates.initialBudget I) h) :=
  (DirectRankHorizonBudget.solve_bound_initial h I hr hc).trans
    (power_three (base_tower (DirectRankPresentationTower.budget_tower I (h+1))) (h+1))

theorem polynomial_eq (S h : Nat) : polynomial S h = 8*h^2+4*S*h+23*h+7*S+3130 := by
  have w₁ : weight DirectRankPresentationTower.expression = 2054 := by decide
  have w₂ : weight exponentExpression = 40 := by decide
  have w₃ : weight baseExpression = 1017 := by decide
  unfold polynomial DirectRankPresentationTower.polynomial DirectRankStateTower.polynomial countExponent rowExponent
  rw [w₁, w₂, w₃]
  ring

theorem solve_explicit_tower (h : Nat) (I : Problem)
    (hr : ∀ i, ArrayAtomExistentialPackages.RowQF (I.rows i)) (hc : ArrayAtomExistentialPackages.RowQF I.candidate) :
    let S := DirectRankHorizonStates.initialBudget I
    ExactReachabilitySize.nodes (DirectExistentialRankCompiler.solve h I hr hc).toFormula+1 ≤
      tower 3 (8*h^2+4*S*h+23*h+7*S+3130) := by
  simpa only [polynomial_eq] using solve_tower h I hr hc

end NSSE.DirectRankFormulaTower
