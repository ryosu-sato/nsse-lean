import NSSE.StoredTupleEnumeration

/-! Materialize a finite relation from a counted tuple predicate. -/
namespace NSSE.StoredRelationMaterialization
open StoredTupleEnumeration
variable {d k : Nat}

def select (p : Tuple d k → Bool × Nat) : List (Tuple d k) → List (Tuple d k) × Nat
  | [] => ([],1)
  | x::xs => let a := p x; let b := select p xs
    (if a.1 then x::b.1 else b.1,3+a.2+b.2)
theorem select_value (p : Tuple d k → Bool × Nat) (xs : List (Tuple d k)) :
    (select p xs).1 = xs.filter (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [select,List.filter_cons,ih]
theorem select_bound (p : Tuple d k → Bool × Nat) (xs : List (Tuple d k)) (c : Nat)
    (hc : ∀ x, (p x).2 ≤ c) : (select p xs).2 ≤ 1+xs.length*(3+c) := by
  induction xs with
  | nil => simp [select]
  | cons x xs ih => have h := hc x; simp only [select,List.length_cons]; nlinarith

def build (p : Tuple d k → Bool × Nat) : StoredFiniteRelations.Relation d (d^k) k × Nat :=
  let e := CountedFinEnumeration.enumerate d
  let a := enumerate e.1 k
  let b := select p a.1
  (⟨b.1,by
    rw [select_value]
    have h := List.length_filter_le (fun x => (p x).1) a.1
    simpa only [a,e,length,CountedFinEnumeration.value,List.length_finRange] using h⟩,3+e.2+a.2+b.2)
theorem rows_value (p : Tuple d k → Bool × Nat) :
    (build p).1.rows = ((enumerate (List.finRange d) k).1.filter (fun x => (p x).1)) := by
  simp only [build,select_value,CountedFinEnumeration.value]

theorem tuple_ext (a b : Tuple d k) (h : a.values=b.values) : a=b := by
  cases a; cases b; cases h; rfl

theorem correct (p : Tuple d k → Bool × Nat) (xs : Tuple d k) :
    (StoredFiniteRelations.interpret k (build p).1 xs).1 = (p xs).1 := by
  apply Bool.eq_iff_iff.mpr
  change (StoredFiniteRelations.scan xs (build p).1.rows).1 = true ↔ (p xs).1 = true
  rw [StoredFiniteRelations.scan_correct,rows_value]
  constructor
  · rintro ⟨row,hrow,heq⟩
    have h := tuple_ext row xs heq
    subst row
    exact (List.mem_filter.mp hrow).2
  · intro h
    exact ⟨xs,List.mem_filter.mpr ⟨complete _ (fun x => List.mem_finRange x) k xs,h⟩,rfl⟩

def budget (d k c : Nat) := 4+(d+1)^2+StoredTupleEnumeration.budget d k+d^k*(3+c)
theorem bound (p : Tuple d k → Bool × Nat) (c : Nat) (hc : ∀ xs, (p xs).2 ≤ c) :
    (build p).2 ≤ budget d k c := by
  have he := CountedFinEnumeration.bound d
  have ha := StoredTupleEnumeration.bound (List.finRange d) k
  have hb := select_bound p (enumerate (List.finRange d) k).1 c hc
  simp only [length,List.length_finRange] at ha hb
  simp only [build,CountedFinEnumeration.value,budget]; omega

theorem exponential_bound (p : Tuple d k → Bool × Nat) (c : Nat) (hc : ∀ xs, (p xs).2 ≤ c) :
    (build p).2 ≤ 4+(d+1)^2+10*(k+1)*(d+1)^(k+1)+d^k*(3+c) := by
  have h := bound p c hc
  have he := StoredTupleEnumeration.budget_bound d k
  unfold budget at h; omega
end NSSE.StoredRelationMaterialization
