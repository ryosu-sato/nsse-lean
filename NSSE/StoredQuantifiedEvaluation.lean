import NSSE.ConcreteValuationEvaluationTower
import NSSE.CountedFinEnumeration
import NSSE.CountedCapEvaluation

/-! Counts domain enumeration, eager quantifier traversal and persistent
valuation extension. Formula construction, index bits and counter arithmetic
are separate obligations. -/
namespace NSSE.StoredQuantifiedEvaluation
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage
open FiniteValuationLookup ExactReachabilitySize
variable {d m n : Nat}

def every {α : Type} (f : α → Bool × Nat) : List α → Bool × Nat
  | [] => (true,1)
  | x::xs => let a := f x; let b := every f xs
    (a.1 && b.1,2+a.2+b.2)
theorem every_value {α : Type} (f : α → Bool × Nat) (xs : List α) :
    (every f xs).1 = true ↔ ∀ x ∈ xs, (f x).1 = true := by
  induction xs <;> simp [every, *]
theorem every_bound {α : Type} (f : α → Bool × Nat) (xs : List α) (c : Nat)
    (hc : ∀ x ∈ xs, (f x).2 ≤ c) : (every f xs).2 ≤ 1+xs.length*(2+c) := by
  induction xs with
  | nil => simp [every]
  | cons x xs ih =>
    have hx := hc x (by simp)
    have ht := ih (fun y hy => hc y (by simp [hy]))
    simp only [every,List.length_cons]; nlinarith

def evaluate (domain : List (Fin d)) (ps : Values d m) :
    {n : Nat} → language.BoundedFormula (Fin m) n → Values d n → Bool × Nat
  | _, .falsum, _ => (false,1)
  | _, .equal t s, vs =>
    let a := term ps vs t; let b := term ps vs s
    let e := equalNat a.1.val b.1.val
    (e.1,1+a.2+b.2+e.2)
  | _, .rel r ts, vs => ConcreteValuationEvaluation.atom ps vs r ts
  | _, .imp f g, vs =>
    let a := evaluate domain ps f vs; let b := evaluate domain ps g vs
    (!a.1 || b.1,1+a.2+b.2)
  | _, .all f, vs =>
    let r := every (fun x => let a := evaluate domain ps f (.snoc vs x)
      (a.1,1+a.2)) domain
    (r.1,1+r.2)

theorem evaluate_correct (domain : List (Fin d)) (complete : ∀ x, x ∈ domain)
    (ps : Values d m) (φ : language.BoundedFormula (Fin m) n) (vs : Values d n) :
    (evaluate domain ps φ vs).1 = true ↔ φ.Realize ps.meaning vs.meaning := by
  induction φ with
  | falsum => simp [evaluate,BoundedFormula.Realize]
  | equal t s => simp [evaluate,equalNat_correct,term_correct,BoundedFormula.Realize,Fin.ext_iff]
  | rel r ts => exact ConcreteValuationEvaluation.atom_correct ps vs r ts
  | imp f g ihf ihg =>
    change ((! (evaluate domain ps f vs).1) || (evaluate domain ps g vs).1) = true ↔ _
    rw [Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff]
    simp only [BoundedFormula.Realize]
    have hf := ihf vs; have hg := ihg vs
    tauto
  | all f ih =>
    simp only [evaluate,every_value,BoundedFormula.Realize]
    constructor
    · intro h x; exact (ih (.snoc vs x)).mp (h x (complete x))
    · intro h x _; exact (ih (.snoc vs x)).mpr (h x)

def weight (d m K l : Nat) := 2*(m+K)+d+3*l+3

theorem evaluate_bound (domain : List (Fin d)) (ps : Values d m)
    (φ : language.BoundedFormula (Fin m) n) (vs : Values d n)
    (K : Nat) (hk : n+nodes φ ≤ K) :
    (evaluate domain ps φ vs).2 ≤
      weight d m K domain.length * CountedFiniteFormulaEvaluation.visits domain.length φ := by
  induction φ with
  | falsum => simp [evaluate,CountedFiniteFormulaEvaluation.visits,weight]
  | equal t s =>
    have ht := term_bound ps vs t; have hs := term_bound ps vs s
    have he := equalFin_bound (term ps vs t).1 (term ps vs s).1
    simp only [evaluate,CountedFiniteFormulaEvaluation.visits,Nat.mul_one,weight]
    simp only [nodes] at hk; omega
  | rel r ts =>
    have ha := ConcreteValuationEvaluation.atom_bound ps vs r ts
    simp only [evaluate,CountedFiniteFormulaEvaluation.visits,Nat.mul_one,weight]
    simp only [nodes] at hk; omega
  | @imp n f g ihf ihg =>
    simp only [nodes] at hk
    have hf := ihf vs (by omega); have hg := ihg vs (by omega)
    have hw : 1 ≤ weight d m K domain.length := by unfold weight; omega
    simp only [evaluate,CountedFiniteFormulaEvaluation.visits]; nlinarith
  | @all n f ih =>
    have hh := every_bound (fun x => let a := evaluate domain ps f (.snoc vs x)
      (a.1,1+a.2)) domain
      (1+weight d m K domain.length * CountedFiniteFormulaEvaluation.visits domain.length f)
      (fun x _ => Nat.add_le_add_left (ih (.snoc vs x) (by simp only [nodes] at hk; omega)) 1)
    have hw : 2+3*domain.length ≤ weight d m K domain.length := by unfold weight; omega
    simp only [evaluate,CountedFiniteFormulaEvaluation.visits]
    nlinarith

def decideFormula (φ : language.Formula (Fin m)) (ps : Values d m) : Bool × Nat :=
  let e := CountedFinEnumeration.enumerate d
  let r := evaluate e.1 ps φ .nil
  (r.1,1+e.2+r.2)
theorem decideFormula_correct (φ : language.Formula (Fin m)) (ps : Values d m) :
    (decideFormula φ ps).1 = true ↔ φ.Realize ps.meaning := by
  simp only [decideFormula,CountedFinEnumeration.value]
  exact evaluate_correct _ (fun x => List.mem_finRange x) ps φ .nil
theorem decideFormula_bound (φ : language.Formula (Fin m)) (ps : Values d m) :
    (decideFormula φ ps).2 ≤ 1+(d+1)^2+
      weight d m (nodes φ) d * (nodes φ*(d+1)^nodes φ) := by
  have he := CountedFinEnumeration.bound d
  have h := evaluate_bound (List.finRange d) ps φ .nil (nodes φ) (by omega)
  simp only [List.length_finRange] at h
  have hv := Nat.mul_le_mul_left (weight d m (nodes φ) d)
    (CountedFiniteFormulaEvaluation.visits_bound d φ)
  have hh := h.trans hv
  simp only [decideFormula,CountedFinEnumeration.value]
  omega
open DirectRankStateTower DirectRankFormulaTower

theorem decideFormula_tower {x : Nat} (φ : language.Formula (Fin m)) (ps : Values d m)
    (hφ : nodes φ ≤ tower 3 x) :
    (decideFormula φ ps).2 ≤ tower 4 (x+m+4*d+17+(d+1)^2) := by
  have h := ConcreteValuationEvaluationTower.weighted_tower hφ (m+2*d+2) d
  have hw : weight d m (nodes φ) d ≤ 2*(m+2*d+2+nodes φ)+d+1 := by
    unfold weight; omega
  have hp := Nat.mul_le_mul_right (nodes φ*((d+1)^nodes φ)) hw
  have ht := hp.trans h
  have ha := CountedCapEvaluation.tower_add 4 (x+(m+2*d+2)+2*d+14) (1+(d+1)^2)
  have hb := decideFormula_bound φ ps
  calc
    _ ≤ tower 4 (x+(m+2*d+2)+2*d+14)+(1+(d+1)^2) := by omega
    _ ≤ _ := by convert ha using 1; congr 1; omega

open SymbolicGuardedBlocks ArrayAtomExistentialPackages
variable {k c : Nat} {ns : Fin k → Nat}

def decideRank (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    (ps : Values d m) : Bool × Nat :=
  decideFormula (DirectExistentialRankCompiler.solve h
    (ConcreteValuationEvaluationTower.problem rows C) hr hc).toFormula ps

theorem decideRank_correct (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    [Nontrivial (Fin d)] (ps : Values d m)
    (hb : RankAvoidanceCompiler.RankBound (ConcreteValuationEvaluationTower.problem rows C)
      ps.meaning h) :
    (decideRank h rows C hr hc ps).1 = true ↔
      RankAvoidanceCompiler.Avoid (ConcreteValuationEvaluationTower.problem rows C) ps.meaning :=
  (decideFormula_correct _ ps).trans
    (DirectExistentialRankCompiler.solve_correct h (ConcreteValuationEvaluationTower.problem rows C) hr hc ps.meaning hb)

theorem decideRank_tower (h : Nat) (rows : (i : Fin k) → Row language (Fin m) (ns i))
    (C : Row language (Fin m) c) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C)
    (ps : Values d m) :
    let S := DirectRankHorizonStates.initialBudget (ConcreteValuationEvaluationTower.problem rows C)
    (decideRank h rows C hr hc ps).2 ≤
      tower 4 (8*h^2+4*S*h+23*h+7*S+m+4*d+3147+(d+1)^2) := by
  let I := ConcreteValuationEvaluationTower.problem rows C
  let S := DirectRankHorizonStates.initialBudget I
  have hs := solve_explicit_tower h I hr hc
  have hn : nodes (DirectExistentialRankCompiler.solve h I hr hc).toFormula ≤
      tower 3 (8*h^2+4*S*h+23*h+7*S+3130) := by
    dsimp only [S]; omega
  have hh := decideFormula_tower (DirectExistentialRankCompiler.solve h I hr hc).toFormula ps hn
  rw [show (8*h^2+4*S*h+23*h+7*S+3130)+m+4*d+17+(d+1)^2 =
    8*h^2+4*S*h+23*h+7*S+m+4*d+3147+(d+1)^2 by omega] at hh
  exact hh
end NSSE.StoredQuantifiedEvaluation
