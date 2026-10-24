import NSSE.StoredPackageBodies

/-! Closing a quantifier-free package matrix with counted syntax construction.
Source unary tuple access, bit costs and machine simulation retain the
accounting boundary stated in StoredFormulaRelabel. -/
namespace NSSE.StoredExistentialClosure
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage
variable {P : Type} {k : Nat}

def term : language.Term ((P ⊕ Fin k) ⊕ Fin 0) → language.Term (P ⊕ Fin k) × Nat
  | .var (.inl x) => (.var x,2)
  | .var (.inr i) => Fin.elim0 i
  | .func f _ => nomatch f

theorem term_value (t : language.Term ((P ⊕ Fin k) ⊕ Fin 0)) :
    (term t).1 = t.relabel (BoundedFormula.relabelAux (fun x : P ⊕ Fin k => x) 0) := by
  cases t with
  | var x =>
    cases x with
    | inl x =>
      cases x with
      | inl p => rfl
      | inr i =>
        simp only [term,Term.relabel,BoundedFormula.relabelAux,Function.comp_apply,Sum.map_inl]
        congr 2
    | inr i => exact Fin.elim0 i
  | func f _ => nomatch f
theorem term_cost (t : language.Term ((P ⊕ Fin k) ⊕ Fin 0)) : (term t).2 = 2 := by
  cases t with
  | var x => cases x with
    | inl x => rfl
    | inr i => exact Fin.elim0 i
  | func f _ => nomatch f

def matrix : (φ : language.Formula (P ⊕ Fin k)) → φ.IsQF → language.BoundedFormula P k × Nat
  | .falsum, _ => (.falsum,1)
  | .equal t s, _ => let a := term t; let b := term s
    (.equal a.1 b.1,1+a.2+b.2)
  | .rel (.unary bs) ts, _ => let a := term (ts 0)
    (.rel (.unary bs) (fun _ => a.1),2+a.2)
  | .imp φ ψ, h =>
    let a := matrix φ (by cases h with | imp hφ _ => exact hφ | of_isAtomic ha => cases ha)
    let b := matrix ψ (by cases h with | imp _ hψ => exact hψ | of_isAtomic ha => cases ha)
    (.imp a.1 b.1,1+a.2+b.2)
  | .all φ, h => False.elim (BoundedFormula.not_all_isQF φ h)

theorem matrix_value (φ : language.Formula (P ⊕ Fin k)) (h : φ.IsQF) :
    (matrix φ h).1 = BoundedFormula.relabel (fun x => x) φ := by
  induction h with
  | falsum => simp [matrix,BoundedFormula.relabel,BoundedFormula.mapTermRel]
  | of_isAtomic ha =>
    cases ha with
    | equal t s => simp only [Term.bdEqual,Relations.boundedFormula,matrix,BoundedFormula.relabel,BoundedFormula.mapTermRel,term_value]
    | rel r ts =>
      change Rel _ at r
      cases r with
      | unary bs =>
        simp only [Term.bdEqual,Relations.boundedFormula,matrix,BoundedFormula.relabel,BoundedFormula.mapTermRel,term_value]
        congr 1
        funext i
        congr 1
        exact congrArg ts (Subsingleton.elim 0 i)
  | imp hφ hψ ihφ ihψ =>
    simp only [matrix,BoundedFormula.relabel_imp,ihφ,ihψ]

theorem matrix_bound (φ : language.Formula (P ⊕ Fin k)) (h : φ.IsQF) :
    (matrix φ h).2 ≤ 5*nodes φ := by
  induction h with
  | falsum => simp [matrix,nodes]
  | of_isAtomic ha =>
    cases ha with
    | equal t s => simp [matrix,term_cost,nodes,Term.bdEqual]
    | rel r ts =>
      change Rel _ at r
      cases r with
      | unary bs => simp [matrix,term_cost,nodes,Relations.boundedFormula]
  | imp hφ hψ ihφ ihψ => simp only [matrix,nodes]; nlinarith

def bindAll : {k : Nat} → language.BoundedFormula P k → language.Formula P × Nat
  | 0, φ => (φ,1)
  | _+1, φ =>
    let r := bindAll (.imp (.all (.imp φ .falsum)) .falsum)
    (r.1,6+r.2)
theorem prefix_value (φ : language.BoundedFormula P k) : (bindAll φ).1 = φ.exs := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _
theorem prefix_cost (φ : language.BoundedFormula P k) : (bindAll φ).2 = 1+6*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bindAll,ih]; omega

def close (φ : language.Formula (P ⊕ Fin k)) (h : φ.IsQF) : language.Formula P × Nat :=
  let a := matrix φ h; let b := bindAll a.1
  (b.1,1+a.2+b.2)
theorem close_value (φ : language.Formula (P ⊕ Fin k)) (h : φ.IsQF) :
    (close φ h).1 = SymbolicReachability.closeColumn φ := by
  simp only [close,prefix_value,matrix_value,SymbolicReachability.closeColumn]
theorem close_bound (φ : language.Formula (P ⊕ Fin k)) (h : φ.IsQF) :
    (close φ h).2 ≤ 2+5*nodes φ+6*k := by
  have hm := matrix_bound φ h
  simp only [close,prefix_cost]; omega

def build (A : Package language P) : language.Formula P × Nat := close A.body A.qfree
theorem value (A : Package language P) : (build A).1 = A.toFormula := close_value _ _
theorem bound (A : Package language P) : (build A).2 ≤ 2+5*nodes A.body+6*A.vars := close_bound _ _
end NSSE.StoredExistentialClosure
