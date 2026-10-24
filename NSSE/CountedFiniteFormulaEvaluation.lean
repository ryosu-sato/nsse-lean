import NSSE.DirectRankFormulaTower

/-! # Actual finite evaluator with an exact formula-visit counter

One unit is charged per visited formula constructor. Atom internals, term
realization and encoding costs are deliberately separate from this counter.
-/

namespace NSSE.CountedFiniteFormulaEvaluation

open FirstOrder FirstOrder.Language ExactReachabilitySize

universe u v w z
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {D : Type z}
variable [L.Structure D] [DecidableEq D]

def evaluate (domain : List D) (relDec : FiniteRankDecision.RelationDecision L D) :
    {n : Nat} → L.BoundedFormula P n → (P → D) → (Fin n → D) → Bool × Nat
  | _, .falsum, _, _ => (false,1)
  | _, .equal t s, p, xs => (decide (t.realize (Sum.elim p xs) = s.realize (Sum.elim p xs)),1)
  | _, .rel r ts, p, xs => (@decide _ (relDec r (fun i => (ts i).realize (Sum.elim p xs))),1)
  | _, .imp f g, p, xs =>
    let a := evaluate domain relDec f p xs
    let b := evaluate domain relDec g p xs
    (!a.1 || b.1,1+a.2+b.2)
  | _, .all f, p, xs =>
    let as := domain.map (fun x => evaluate domain relDec f p (Fin.snoc xs x))
    (as.all Prod.fst,1+(as.map Prod.snd).sum)

def visits (d : Nat) : {n : Nat} → L.BoundedFormula P n → Nat
  | _, .falsum => 1
  | _, .equal _ _ => 1
  | _, .rel _ _ => 1
  | _, .imp f g => 1+visits d f+visits d g
  | _, .all f => 1+d*visits d f

theorem visits_exact (domain : List D) (relDec : FiniteRankDecision.RelationDecision L D)
    {n : Nat} (φ : L.BoundedFormula P n) (p : P → D) (xs : Fin n → D) :
    (evaluate domain relDec φ p xs).2 = visits domain.length φ := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp f g ihf ihg => simp only [evaluate, visits, ihf, ihg]
  | all f ih =>
    simp only [evaluate, visits, List.map_map, Function.comp_def, ih]
    simp

theorem evaluate_correct (domain : List D) (complete : ∀ x, x ∈ domain)
    (relDec : FiniteRankDecision.RelationDecision L D) {n : Nat} (φ : L.BoundedFormula P n)
    (p : P → D) (xs : Fin n → D) :
    (evaluate domain relDec φ p xs).1 = true ↔ φ.Realize p xs := by
  induction φ with
  | falsum => simp [evaluate, BoundedFormula.Realize]
  | equal t s => simp [evaluate, BoundedFormula.Realize]
  | rel r ts => simp [evaluate, BoundedFormula.Realize]
  | imp f g ihf ihg =>
    change ((! (evaluate domain relDec f p xs).1) || (evaluate domain relDec g p xs).1) = true ↔ _
    rw [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    simp only [ihf, ihg, BoundedFormula.Realize]
    have hf := ihf xs
    have hg := ihg xs
    tauto
  | all f ih =>
    simp only [evaluate, List.all_eq_true, List.mem_map, Prod.forall, BoundedFormula.Realize]
    constructor
    · intro h x
      apply (ih (Fin.snoc xs x)).mp
      exact h _ _ ⟨x,complete x,rfl⟩
    · intro h a b hab
      obtain ⟨x,_,he⟩ := hab
      have hx := (ih (Fin.snoc xs x)).mpr (h x)
      simpa only [he] using hx

theorem nodes_pos {n : Nat} (φ : L.BoundedFormula P n) : 1 ≤ nodes φ := by
  cases φ <;> simp only [nodes] <;> omega

theorem visits_bound (d : Nat) {n : Nat} (φ : L.BoundedFormula P n) :
    visits d φ ≤ nodes φ*(d+1)^nodes φ := by
  induction φ with
  | falsum => simp [visits, nodes]
  | equal _ _ => simp [visits, nodes]
  | rel _ _ => simp [visits, nodes]
  | imp f g ihf ihg =>
    have hf := ihf.trans (Nat.mul_le_mul_left (nodes f)
      (Nat.pow_le_pow_right (by omega : 1 ≤ d+1) (by omega : nodes f ≤ 1+nodes f+nodes g)))
    have hg := ihg.trans (Nat.mul_le_mul_left (nodes g)
      (Nat.pow_le_pow_right (by omega : 1 ≤ d+1) (by omega : nodes g ≤ 1+nodes f+nodes g)))
    have h₁ : 1 ≤ (d+1)^(1+nodes f+nodes g) := Nat.one_le_pow _ _ (by omega)
    simp only [visits, nodes]
    nlinarith
  | all f ih =>
    have h₁ : 1 ≤ (d+1)^nodes f := Nat.one_le_pow _ _ (by omega)
    simp only [visits, nodes]
    rw [show 1+nodes f = nodes f+1 by omega, pow_succ]
    nlinarith

theorem evaluated_visits_bound (domain : List D) (relDec : FiniteRankDecision.RelationDecision L D)
    {n : Nat} (φ : L.BoundedFormula P n) (p : P → D) (xs : Fin n → D) :
    (evaluate domain relDec φ p xs).2 ≤ nodes φ*(domain.length+1)^nodes φ := by
  rw [visits_exact]
  exact visits_bound _ _

end NSSE.CountedFiniteFormulaEvaluation
