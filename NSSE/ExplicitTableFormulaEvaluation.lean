import NSSE.ExplicitFiniteTableRows

/-! Formula traversal plus actual linear Boolean-table lookup counts.
This metric still excludes valuation lookup, equality bit operations,
allocation, arithmetic on counters and construction of the formula. -/

namespace NSSE.ExplicitTableFormulaEvaluation

open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize

variable {d : Nat} {P : Type*}

def relation : {k : Nat} → Rel k → (Fin k → Fin d) → Bool × Nat
  | _, .unary bs, xs => lookup bs (xs 0).val

theorem relation_bound {k : Nat} (r : Rel k) (xs : Fin k → Fin d) :
    (relation r xs).2 ≤ d := by
  cases r with
  | unary bs => exact lookup_bound bs (xs 0)

def evaluate (domain : List (Fin d)) :
    {n : Nat} → language.BoundedFormula P n → (P → Fin d) → (Fin n → Fin d) → Bool × Nat
  | _, .falsum, _, _ => (false,1)
  | _, .equal t s, p, xs => (decide (t.realize (Sum.elim p xs) = s.realize (Sum.elim p xs)),1)
  | _, .rel r ts, p, xs => let a := relation r (fun i => (ts i).realize (Sum.elim p xs))
    (a.1,1+a.2)
  | _, .imp f g, p, xs =>
    let a := evaluate domain f p xs
    let b := evaluate domain g p xs
    (!a.1 || b.1,1+a.2+b.2)
  | _, .all f, p, xs =>
    let as := domain.map (fun x => evaluate domain f p (Fin.snoc xs x))
    (as.all Prod.fst,1+(as.map Prod.snd).sum)

theorem evaluate_correct (domain : List (Fin d)) (complete : ∀ x, x ∈ domain)
    {n : Nat} (φ : language.BoundedFormula P n)
    (p : P → Fin d) (xs : Fin n → Fin d) :
    (evaluate domain φ p xs).1 = true ↔ φ.Realize p xs := by
  induction φ with
  | falsum => simp [evaluate, BoundedFormula.Realize]
  | equal t s => simp [evaluate, BoundedFormula.Realize]
  | rel r ts =>
    change Rel _ at r
    cases r with
    | unary bs => rfl
  | imp f g ihf ihg =>
    change ((! (evaluate domain f p xs).1) || (evaluate domain g p xs).1) = true ↔ _
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


theorem evaluate_bound (domain : List (Fin d)) {n : Nat}
    (φ : language.BoundedFormula P n) (p : P → Fin d) (xs : Fin n → Fin d) :
    (evaluate domain φ p xs).2 ≤ (d+1)*CountedFiniteFormulaEvaluation.visits domain.length φ := by
  induction φ with
  | falsum => simp [evaluate, CountedFiniteFormulaEvaluation.visits]
  | equal t s => simp [evaluate, CountedFiniteFormulaEvaluation.visits]
  | rel r ts =>
    have h := relation_bound r (fun i => (ts i).realize (Sum.elim p xs))
    simp only [evaluate, CountedFiniteFormulaEvaluation.visits, Nat.mul_one]
    omega
  | imp f g ihf ihg =>
    have hf := ihf xs
    have hg := ihg xs
    simp only [evaluate, CountedFiniteFormulaEvaluation.visits]
    nlinarith
  | all f ih =>
    have hh := DirectRankHorizonStates.sum_map_le domain
      (fun x => (evaluate domain f p (Fin.snoc xs x)).2)
      ((d+1)*CountedFiniteFormulaEvaluation.visits domain.length f) (fun x _ => ih _)
    simp only [evaluate, List.map_map, Function.comp_def, CountedFiniteFormulaEvaluation.visits]
    nlinarith

theorem evaluate_nodes_bound (domain : List (Fin d)) {n : Nat}
    (φ : language.BoundedFormula P n) (p : P → Fin d) (xs : Fin n → Fin d) :
    (evaluate domain φ p xs).2 ≤ (d+1)*(nodes φ*(domain.length+1)^nodes φ) :=
  (evaluate_bound domain φ p xs).trans
    (Nat.mul_le_mul_left _ (CountedFiniteFormulaEvaluation.visits_bound _ _))

/-- Evaluation on the actual full finite alphabet, including empty/singleton alphabets. -/
def decideFormula (φ : language.Formula P) (p : P → Fin d) : Bool × Nat :=
  evaluate (List.finRange d) φ p Fin.elim0

theorem decideFormula_correct (φ : language.Formula P) (p : P → Fin d) :
    (decideFormula φ p).1 = true ↔ φ.Realize p :=
  evaluate_correct _ (fun x => List.mem_finRange x) φ p Fin.elim0

theorem decideFormula_bound (φ : language.Formula P) (p : P → Fin d) :
    (decideFormula φ p).2 ≤ (d+1)*(nodes φ*(d+1)^nodes φ) := by
  simpa only [decideFormula, List.length_finRange] using
    evaluate_nodes_bound (List.finRange d) φ p Fin.elim0

end NSSE.ExplicitTableFormulaEvaluation
