import NSSE.FiniteValuationLookup

/-! Formula, table and valuation structural lookup counts for an executable
finite evaluator. Index bits, allocation and arithmetic on counters
are not yet included in this metric. -/

namespace NSSE.ConcreteValuationEvaluation

open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage
open FiniteValuationLookup ExactReachabilitySize

variable {d m n : Nat}

def atom (ps : Values d m) (vs : Values d n) :
    {k : Nat} → Rel k → (Fin k → language.Term (Fin m ⊕ Fin n)) → Bool × Nat
  | _, .unary bs, ts =>
    let v := term ps vs (ts 0)
    let r := lookup bs v.1.val
    (r.1,1+v.2+r.2)

theorem atom_correct (ps : Values d m) (vs : Values d n) {k : Nat}
    (r : Rel k) (ts : Fin k → language.Term (Fin m ⊕ Fin n)) :
    (atom ps vs r ts).1 = true ↔
      Structure.RelMap (L := language) r (fun i => (ts i).realize (Sum.elim ps.meaning vs.meaning)) := by
  cases r with
  | unary bs =>
    change (lookup bs (term ps vs (ts 0)).1.val).1 = true ↔ _
    rw [term_correct]
    rfl

theorem atom_bound (ps : Values d m) (vs : Values d n) {k : Nat}
    (r : Rel k) (ts : Fin k → language.Term (Fin m ⊕ Fin n)) :
    (atom ps vs r ts).2 ≤ 1+(m+n)+d := by
  cases r with
  | unary bs =>
    have ht := term_bound ps vs (ts 0)
    have hl := lookup_bound bs (term ps vs (ts 0)).1
    simp only [atom]
    omega

def evaluate (domain : List (Fin d)) (ps : Values d m) :
    {n : Nat} → language.BoundedFormula (Fin m) n → Values d n → Bool × Nat
  | _, .falsum, _ => (false,1)
  | _, .equal t s, vs =>
    let a := term ps vs t
    let b := term ps vs s
    let e := equalNat a.1.val b.1.val
    (e.1,1+a.2+b.2+e.2)
  | _, .rel r ts, vs => atom ps vs r ts
  | _, .imp f g, vs =>
    let a := evaluate domain ps f vs
    let b := evaluate domain ps g vs
    (!a.1 || b.1,1+a.2+b.2)
  | _, .all f, vs =>
    let as := domain.map (fun x => evaluate domain ps f (.snoc vs x))
    (as.all Prod.fst,1+(as.map Prod.snd).sum)

theorem evaluate_correct (domain : List (Fin d)) (complete : ∀ x, x ∈ domain)
    (ps : Values d m) (φ : language.BoundedFormula (Fin m) n) (vs : Values d n) :
    (evaluate domain ps φ vs).1 = true ↔ φ.Realize ps.meaning vs.meaning := by
  induction φ with
  | falsum => simp [evaluate, BoundedFormula.Realize]
  | equal t s => simp [evaluate, equalNat_correct, term_correct, BoundedFormula.Realize, Fin.ext_iff]
  | rel r ts => exact atom_correct ps vs r ts
  | imp f g ihf ihg =>
    change ((! (evaluate domain ps f vs).1) || (evaluate domain ps g vs).1) = true ↔ _
    rw [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    simp only [BoundedFormula.Realize]
    have hf := ihf vs
    have hg := ihg vs
    tauto
  | all f ih =>
    simp only [evaluate, List.all_eq_true, List.mem_map, Prod.forall, BoundedFormula.Realize]
    constructor
    · intro h x
      exact (ih (.snoc vs x)).mp (h _ _ ⟨x,complete x,rfl⟩)
    · intro h a b hab
      obtain ⟨x,_,he⟩ := hab
      have hx := (ih (.snoc vs x)).mpr (h x)
      simpa only [he] using hx

theorem evaluate_bound (domain : List (Fin d)) (ps : Values d m)
    (φ : language.BoundedFormula (Fin m) n) (vs : Values d n)
    (K : Nat) (hk : n+nodes φ ≤ K) :
    (evaluate domain ps φ vs).2 ≤
      (2*(m+K)+d+1)*CountedFiniteFormulaEvaluation.visits domain.length φ := by
  induction φ with
  | falsum => simp [evaluate, CountedFiniteFormulaEvaluation.visits]
  | equal t s =>
    have ht := term_bound ps vs t
    have hs := term_bound ps vs s
    have he := equalFin_bound (term ps vs t).1 (term ps vs s).1
    simp only [evaluate, CountedFiniteFormulaEvaluation.visits, Nat.mul_one]
    simp only [nodes] at hk
    omega
  | rel r ts =>
    have ha := atom_bound ps vs r ts
    simp only [evaluate, CountedFiniteFormulaEvaluation.visits, Nat.mul_one]
    simp only [nodes] at hk
    omega
  | @imp n f g ihf ihg =>
    simp only [nodes] at hk
    have hf := ihf vs (by omega)
    have hg := ihg vs (by omega)
    simp only [evaluate, CountedFiniteFormulaEvaluation.visits]
    nlinarith
  | @all n f ih =>
    have hh := DirectRankHorizonStates.sum_map_le domain
      (fun x => (evaluate domain ps f (.snoc vs x)).2)
      ((2*(m+K)+d+1)*CountedFiniteFormulaEvaluation.visits domain.length f)
      (fun x _ => ih (.snoc vs x) (by simp only [nodes] at hk; omega))
    simp only [evaluate, List.map_map, Function.comp_def, CountedFiniteFormulaEvaluation.visits]
    nlinarith

def decideFormula (φ : language.Formula (Fin m)) (ps : Values d m) : Bool × Nat :=
  evaluate (List.finRange d) ps φ .nil

theorem decideFormula_correct (φ : language.Formula (Fin m)) (ps : Values d m) :
    (decideFormula φ ps).1 = true ↔ φ.Realize ps.meaning :=
  evaluate_correct _ (fun x => List.mem_finRange x) ps φ .nil

theorem decideFormula_bound (φ : language.Formula (Fin m)) (ps : Values d m) :
    (decideFormula φ ps).2 ≤
      (2*(m+nodes φ)+d+1)*(nodes φ*(d+1)^nodes φ) := by
  have h := evaluate_bound (List.finRange d) ps φ .nil (nodes φ) (by omega)
  have hb := Nat.mul_le_mul_left (2*(m+nodes φ)+d+1)
    (CountedFiniteFormulaEvaluation.visits_bound d φ)
  exact h.trans (by simpa only [List.length_finRange] using hb)

end NSSE.ConcreteValuationEvaluation
