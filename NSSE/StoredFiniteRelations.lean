import NSSE.StoredRelationalEvaluation

/-! Concrete finite relations represented by stored accepted tuples.
The row-count certificate erases; interpretation scans actual lists. -/
namespace NSSE.StoredFiniteRelations
open FirstOrder FirstOrder.Language FiniteValuationLookup StoredRelationalFormula
variable {d t k m : Nat}

structure Relation (d t k : Nat) where
  rows : List (StoredRelationTuple.Data (Fin d) k)
  bounded : rows.length ≤ t
abbrev language (d t : Nat) := UniformWordLowering.wordLanguage (Relation d t)
instance model : (language d t).Structure (Fin d) where
  funMap f := nomatch f
  RelMap r xs := ∃ row ∈ r.rows, row.values = List.ofFn xs

def equal : List (Fin d) → List (Fin d) → Bool × Nat
  | [],[] => (true,1)
  | [],_::_ => (false,1)
  | _::_,[] => (false,1)
  | x::xs,y::ys => let a := equalNat x.val y.val; let b := equal xs ys
    (a.1 && b.1,2+a.2+b.2)
theorem equal_correct (xs ys : List (Fin d)) : (equal xs ys).1 = true ↔ xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equal]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equal]
    | cons y ys => simp [equal,equalNat_correct,ih,Fin.ext_iff]
theorem equal_bound (xs ys : List (Fin d)) : (equal xs ys).2 ≤ 1+xs.length*(2+d) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equal]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equal]
    | cons y ys =>
      have he := equalFin_bound x y
      have hb := ih ys
      simp only [equal,List.length_cons]; nlinarith

def scan (xs : StoredRelationTuple.Data (Fin d) k) : List (StoredRelationTuple.Data (Fin d) k) → Bool × Nat
  | [] => (false,1)
  | row::rs => let a := equal xs.values row.values; let b := scan xs rs
    (a.1 || b.1,2+a.2+b.2)
theorem scan_correct (xs : StoredRelationTuple.Data (Fin d) k) (rs : List (StoredRelationTuple.Data (Fin d) k)) :
    (scan xs rs).1 = true ↔ ∃ row ∈ rs, row.values = xs.values := by
  induction rs with
  | nil => simp [scan]
  | cons row rs ih =>
    simp only [scan,Bool.or_eq_true,equal_correct,ih,List.mem_cons]
    constructor
    · rintro (h | ⟨r,hr,he⟩)
      · exact ⟨row,Or.inl rfl,h.symm⟩
      · exact ⟨r,Or.inr hr,he⟩
    · rintro ⟨r,(hr | hr),he⟩
      · subst r; exact Or.inl he.symm
      · exact Or.inr ⟨r,hr,he⟩
theorem scan_bound (xs : StoredRelationTuple.Data (Fin d) k) (rs : List (StoredRelationTuple.Data (Fin d) k)) :
    (scan xs rs).2 ≤ 1+rs.length*(3+k*(2+d)) := by
  induction rs with
  | nil => simp [scan]
  | cons row rs ih =>
    have he := equal_bound xs.values row.values
    rw [xs.length] at he
    simp only [scan,List.length_cons]; nlinarith

theorem ofFn_read (xs : StoredRelationTuple.Data (Fin d) k) :
    List.ofFn (fun i => (StoredRelationTuple.read xs i).1) = xs.values := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,xs.length]
  · intro i hi hj
    simp only [List.getElem_ofFn,StoredRelationTuple.read_value]

def interpret : StoredRelationalEvaluation.Interpreter (Relation d t) d := fun _ r xs =>
  let a := scan xs r.rows
  (a.1,1+a.2)
theorem interpret_correct (r : Relation d t k) (xs : StoredRelationTuple.Data (Fin d) k) :
    (interpret k r xs).1 = true ↔
      Structure.RelMap (L := language d t) r (fun i => (StoredRelationTuple.read xs i).1) := by
  change (scan xs r.rows).1 = true ↔ ∃ row ∈ r.rows, row.values = List.ofFn _
  rw [scan_correct,ofFn_read]
def budget (d t K : Nat) := 2+t*(3+K*(2+d))
theorem interpret_bound (K : Nat) (hk : k ≤ K) (r : Relation d t k) (xs : StoredRelationTuple.Data (Fin d) k) :
    (interpret k r xs).2 ≤ budget d t K := by
  have h := scan_bound xs r.rows
  have hm : r.rows.length*(3+k*(2+d)) ≤ t*(3+K*(2+d)) := by
    gcongr
    exact r.bounded
  simp only [interpret,budget]; omega

def decide (φ : Data (Relation d t) (Fin m) 0) (ps : Values d m) : Bool × Nat :=
  StoredRelationalEvaluation.decideFormula interpret φ ps
theorem decide_correct (φ : Data (Relation d t) (Fin m) 0) (ps : Values d m) :
    (decide φ ps).1 = true ↔ Formula.Realize (denote φ) ps.meaning :=
  StoredRelationalEvaluation.decide_correct interpret (fun _ => interpret_correct) φ ps

theorem decide_bound (φ : Data (Relation d t) (Fin m) 0) (ps : Values d m) (K : Nat) (hk : arity φ ≤ K) :
    (decide φ ps).2 ≤ 1+(d+1)^2+
      StoredRelationalEvaluation.weight d m (nodes φ) K d (budget d t K) * (nodes φ*(d+1)^nodes φ) :=
  StoredRelationalEvaluation.decide_bound interpret φ ps K (budget d t K)
    (fun _ hk => interpret_bound K hk) hk
end NSSE.StoredFiniteRelations
