import NSSE.StoredExistentialClosure
import NSSE.TowerExpression

/-! Package-to-formula construction plus finite evaluation. Constructing
the input Package (including rank recursion) is not included in this counter. -/
namespace NSSE.ConstructedPackageEvaluation
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage FiniteValuationLookup
open DirectRankStateTower DirectRankFormulaTower
variable {d m : Nat}

def decide (A : Package language (Fin m)) (ps : Values d m) : Bool × Nat :=
  let a := StoredExistentialClosure.build A
  let b := StoredQuantifiedEvaluation.decideFormula a.1 ps
  (b.1,1+a.2+b.2)

theorem correct (A : Package language (Fin m)) (ps : Values d m) :
    (decide A ps).1 = true ↔ A.toFormula.Realize ps.meaning := by
  simp only [decide,StoredExistentialClosure.value,StoredQuantifiedEvaluation.decideFormula_correct]

def size (A : Package language (Fin m)) := nodes A.body+5*A.vars

theorem size_value (A : Package language (Fin m)) : nodes A.toFormula = size A := by
  simp only [Package.toFormula,nodes_closeColumn,size]

def budget (d : Nat) (A : Package language (Fin m)) :=
  4+5*nodes A.body+6*A.vars+(d+1)^2+
    StoredQuantifiedEvaluation.weight d m (size A) d*(size A*(d+1)^size A)

theorem bound (A : Package language (Fin m)) (ps : Values d m) :
    (decide A ps).2 ≤ budget d A := by
  have ha := StoredExistentialClosure.bound A
  have hb := StoredQuantifiedEvaluation.decideFormula_bound A.toFormula ps
  rw [size_value] at hb
  simp only [decide,StoredExistentialClosure.value,budget]
  omega

def overhead : PolynomialTowerEnvelope.Expr := 3+5*.var 0+6*.var 1

theorem tower_bound {x : Nat} (A : Package language (Fin m)) (ps : Values d m)
    (ha : size A ≤ tower 3 x) :
    (decide A ps).2 ≤ tower 4 (x+m+4*d+41+(d+1)^2) := by
  have hv : ∀ i : Fin 4, (![nodes A.body,A.vars,0,0] : Fin 4 → Nat) i ≤ tower 3 x := by
    intro i; fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons]
    · exact (show nodes A.body ≤ size A by unfold size; omega).trans ha
    · exact (show A.vars ≤ size A by unfold size; omega).trans ha
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have ho := envelope_three overhead ![nodes A.body,A.vars,0,0] x hv
  change 3+5*nodes A.body+6*A.vars ≤ tower 3 (x+21) at ho
  have hc := StoredExistentialClosure.bound A
  have hn : nodes A.toFormula ≤ tower 3 x := by rw [size_value]; exact ha
  have he := StoredQuantifiedEvaluation.decideFormula_tower A.toFormula ps hn
  let y := x+m+4*d+40+(d+1)^2
  have he' : (StoredQuantifiedEvaluation.decideFormula A.toFormula ps).2 ≤ tower 4 y :=
    he.trans (tower_mono 4 (by dsimp [y]; omega))
  have hc' : 1+(StoredExistentialClosure.build A).2 ≤ tower 4 y := by
    apply (show 1+(StoredExistentialClosure.build A).2 ≤ 3+5*nodes A.body+6*A.vars by omega).trans
    apply ho.trans
    exact (TowerExpression.height_mono 3 4 (x+21) (by omega)).trans
      (tower_mono 4 (by dsimp [y]; omega))
  have hh := TowerExpression.double_step 3 y
  simp only [decide,StoredExistentialClosure.value]
  calc
    _ ≤ 2*tower 4 y := by omega
    _ ≤ _ := by convert hh using 1; congr 1; dsimp [y]; omega

open SymbolicGuardedBlocks ArrayAtomExistentialPackages
variable {k c : Nat} {ns : Fin k → Nat}
def decideRank (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    (ps : Values d m) : Bool × Nat :=
  decide (DirectExistentialRankCompiler.solve h (ConcreteValuationEvaluationTower.problem rows C) hr hc) ps

theorem rank_correct (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    [Nontrivial (Fin d)] (ps : Values d m)
    (hb : RankAvoidanceCompiler.RankBound (ConcreteValuationEvaluationTower.problem rows C) ps.meaning h) :
    (decideRank h rows C hr hc ps).1 = true ↔
      RankAvoidanceCompiler.Avoid (ConcreteValuationEvaluationTower.problem rows C) ps.meaning :=
  (correct _ ps).trans (DirectExistentialRankCompiler.solve_correct h
    (ConcreteValuationEvaluationTower.problem rows C) hr hc ps.meaning hb)

theorem rank_tower (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    (ps : Values d m) :
    let S := DirectRankHorizonStates.initialBudget (ConcreteValuationEvaluationTower.problem rows C)
    (decideRank h rows C hr hc ps).2 ≤
      tower 4 (8*h^2+4*S*h+23*h+7*S+m+4*d+3171+(d+1)^2) := by
  let I := ConcreteValuationEvaluationTower.problem rows C
  let S := DirectRankHorizonStates.initialBudget I
  have hs := solve_explicit_tower h I hr hc
  have hn : size (DirectExistentialRankCompiler.solve h I hr hc) ≤
      tower 3 (8*h^2+4*S*h+23*h+7*S+3130) := by
    rw [← size_value]
    dsimp only [S]; omega
  have hh := tower_bound (DirectExistentialRankCompiler.solve h I hr hc) ps hn
  rw [show (8*h^2+4*S*h+23*h+7*S+3130)+m+4*d+41+(d+1)^2 =
    8*h^2+4*S*h+23*h+7*S+m+4*d+3171+(d+1)^2 by omega] at hh
  exact hh
end NSSE.ConstructedPackageEvaluation
