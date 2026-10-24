import NSSE.ExplicitTableFormulaEvaluation

/-! Explicit finite valuations: structural lookup counts, with no callback.
Index comparison/representation and counter arithmetic are separate costs. -/

namespace NSSE.FiniteValuationLookup

open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage

variable {d m n : Nat}

inductive Values (d : Nat) : Nat → Type
  | nil : Values d 0
  | snoc {n : Nat} : Values d n → Fin d → Values d (n+1)

def Values.meaning : {n : Nat} → Values d n → Fin n → Fin d
  | _, .nil => Fin.elim0
  | _, .snoc vs x => Fin.snoc vs.meaning x

def Values.lookup : {n : Nat} → Values d n → Fin n → Fin d × Nat
  | _, .nil, i => Fin.elim0 i
  -- 2026-09-14, v1558: Fin.lastCases uses eager reverseInduction in
  -- Lean 4.19 and performs unused recursive lookups. Test the index
  -- directly instead. Index representation/comparison costs remain separate.
  | _, @Values.snoc _ n vs x, i =>
      if h : i.val = n then (x,1)
      else let r := vs.lookup ⟨i.val,by omega⟩; (r.1,r.2+1)

theorem Values.lookup_correct (vs : Values d n) (i : Fin n) :
    (vs.lookup i).1 = vs.meaning i := by
  induction vs with
  | nil => exact Fin.elim0 i
  | @snoc n vs x ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Values.lookup, Values.meaning]
    · have hj : j.val ≠ n := by omega
      simp [Values.lookup, Values.meaning, ih, hj]

theorem Values.lookup_bound (vs : Values d n) (i : Fin n) :
    (vs.lookup i).2 ≤ n := by
  induction vs with
  | nil => exact Fin.elim0 i
  | @snoc n vs x ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Values.lookup]
    · have hj : j.val ≠ n := by omega
      simpa only [Values.lookup, Fin.coe_castSucc, dif_neg hj] using Nat.add_le_add_right (ih j) 1

def term (ps : Values d m) (vs : Values d n) : language.Term (Fin m ⊕ Fin n) → Fin d × Nat
  | .var (.inl i) => ps.lookup i
  | .var (.inr i) => vs.lookup i
  | .func f _ => nomatch f

theorem term_correct (ps : Values d m) (vs : Values d n)
    (t : language.Term (Fin m ⊕ Fin n)) :
    (term ps vs t).1 = t.realize (Sum.elim ps.meaning vs.meaning) := by
  cases t with
  | var i => cases i <;> simp [term, Values.lookup_correct, Term.realize]
  | func f _ => nomatch f

theorem term_bound (ps : Values d m) (vs : Values d n)
    (t : language.Term (Fin m ⊕ Fin n)) : (term ps vs t).2 ≤ m+n := by
  cases t with
  | var i =>
    cases i with
    | inl i => exact (ps.lookup_bound i).trans (by omega)
    | inr i => exact (vs.lookup_bound i).trans (by omega)
  | func f _ => nomatch f

/-- Unary structural equality; no opaque equality decision in the evaluator. -/
def equalNat : Nat → Nat → Bool × Nat
  | 0, 0 => (true,1)
  | 0, _+1 => (false,1)
  | _+1, 0 => (false,1)
  | a+1, b+1 => let r := equalNat a b; (r.1,r.2+1)

theorem equalNat_correct (a b : Nat) : (equalNat a b).1 = true ↔ a=b := by
  induction a generalizing b with
  | zero => cases b <;> simp [equalNat]
  | succ a ih => cases b <;> simp [equalNat, ih]

theorem equalNat_bound (a b : Nat) : (equalNat a b).2 ≤ a+1 := by
  induction a generalizing b with
  | zero => cases b <;> simp [equalNat]
  | succ a ih =>
    cases b with
    | zero => simp [equalNat]
    | succ b => simpa only [equalNat] using Nat.add_le_add_right (ih b) 1

theorem equalFin_bound (a b : Fin d) : (equalNat a.val b.val).2 ≤ d :=
  (equalNat_bound _ _).trans a.isLt

end NSSE.FiniteValuationLookup
