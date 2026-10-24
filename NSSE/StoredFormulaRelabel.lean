import NSSE.StoredQuantifiedEvaluation

/-! Counted capture-free free-variable relabeling in the concrete unary
language. The supplied name operation has an explicit counter. Relation
lists are shared, not recopied; their evaluation is charged separately. -/
namespace NSSE.StoredFormulaRelabel
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
variable {P Q : Type} {n : Nat}

def term (f : P → Q × Nat) : language.Term (P ⊕ Fin n) → language.Term (Q ⊕ Fin n) × Nat
  | .var (.inl p) => let r := f p; (.var (.inl r.1),2+r.2)
  | .var (.inr i) => (.var (.inr i),2)
  | .func f _ => nomatch f

theorem term_value (f : P → Q × Nat) (t : language.Term (P ⊕ Fin n)) :
    (term f t).1 = t.relabel (Sum.map (fun p => (f p).1) id) := by
  cases t with
  | var x => cases x <;> rfl
  | func f _ => nomatch f

theorem term_bound (f : P → Q × Nat) (b : Nat) (hf : ∀ p, (f p).2 ≤ b)
    (t : language.Term (P ⊕ Fin n)) : (term f t).2 ≤ 2+b := by
  cases t with
  | var x => cases x with
    | inl p => exact Nat.add_le_add_left (hf p) 2
    | inr i => simp only [term]; omega
  | func f _ => nomatch f

def build (f : P → Q × Nat) : {n : Nat} → language.BoundedFormula P n → language.BoundedFormula Q n × Nat
  | _, .falsum => (.falsum,1)
  | _, .equal t s => let a := term f t; let b := term f s
    (.equal a.1 b.1,1+a.2+b.2)
  | _, .rel (.unary bs) ts => let a := term f (ts 0)
    (.rel (.unary bs) (fun _ => a.1),2+a.2)
  | _, .imp φ ψ => let a := build f φ; let b := build f ψ
    (.imp a.1 b.1,1+a.2+b.2)
  | _, .all φ => let a := build f φ; (.all a.1,1+a.2)

def spec (f : P → Q) (φ : language.BoundedFormula P n) : language.BoundedFormula Q n :=
  φ.mapTermRel (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)

theorem value (f : P → Q × Nat) (φ : language.BoundedFormula P n) :
    (build f φ).1 = spec (fun p => (f p).1) φ := by
  induction φ with
  | falsum => rfl
  | equal t s => simp only [build,spec,BoundedFormula.mapTermRel,term_value]
  | rel r ts =>
    change Rel _ at r
    cases r with
    | unary bs =>
      simp only [build,spec,BoundedFormula.mapTermRel,term_value]
      congr 1
      funext i
      congr 1
      exact congrArg ts (Subsingleton.elim 0 i)
  | imp φ ψ ihφ ihψ => simp only [build,spec,BoundedFormula.mapTermRel] at *; rw [ihφ,ihψ]
  | all φ ih => simp only [build,spec,BoundedFormula.mapTermRel] at *; rw [ih]; rfl

theorem bound (f : P → Q × Nat) (b : Nat) (hf : ∀ p, (f p).2 ≤ b)
    (φ : language.BoundedFormula P n) : (build f φ).2 ≤ (5+2*b)*nodes φ := by
  induction φ with
  | falsum => simp only [build,nodes,Nat.mul_one]; omega
  | equal t s =>
    have ht := term_bound f b hf t; have hs := term_bound f b hf s
    simp only [build,nodes,Nat.mul_one]; omega
  | rel r ts =>
    change Rel _ at r
    cases r with
    | unary bs =>
      have ht := term_bound f b hf (ts 0)
      simp only [build,nodes,Nat.mul_one]; omega
  | imp φ ψ ihφ ihψ => simp only [build,nodes]; nlinarith
  | all φ ih => simp only [build,nodes]; nlinarith

theorem names_cast (f : P → Q) (k : Nat) :
    Sum.map id (Fin.castLE (Nat.zero_add k).symm.le) ∘ Sum.map f id =
      BoundedFormula.relabelAux (Sum.inl ∘ f) k := by
  funext x
  cases x with
  | inl p => rfl
  | inr i =>
    simp only [Function.comp_def,Sum.map_inr,BoundedFormula.relabelAux]
    congr 1
    apply Fin.ext
    simp

theorem spec_cast (f : P → Q) (φ : language.BoundedFormula P n) :
    (spec f φ).castLE (Nat.zero_add n).symm.le = φ.relabel (Sum.inl ∘ f) := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [spec,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      Term.relabel_relabel,names_cast,BoundedFormula.relabel]
  | rel r ts =>
    simp only [spec,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      Function.comp_apply,Term.relabel_relabel,names_cast,BoundedFormula.relabel]
    congr 1
    funext i
    simp only [Function.comp_apply,Term.relabel_relabel,names_cast]
  | imp φ ψ ihφ ihψ =>
    simp only [spec,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      BoundedFormula.relabel_imp] at *
    rw [ihφ,ihψ]
  | all φ ih =>
    simp only [spec,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      BoundedFormula.relabel_all,id_eq] at *
    rw [ih]

theorem spec_relabel (f : P → Q) (φ : language.Formula P) : spec f φ = φ.relabel f := by
  simpa only [BoundedFormula.castLE_rfl,Formula.relabel] using spec_cast f φ

theorem formula_value (f : P → Q × Nat) (φ : language.Formula P) :
    (build f φ).1 = φ.relabel (fun p => (f p).1) :=
  (value f φ).trans (spec_relabel _ _)
end NSSE.StoredFormulaRelabel
