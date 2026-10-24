import NSSE.StoredBoundedPeriods

/-! Counted checks for the structural validity needed by period constructors.
This tests the accessed start/transition indices; it is not a canonical-shape
checker (extra entries and defaulted missing entries are permitted). -/
namespace NSSE.StoredDFAValidity
variable {d : Nat}

def allFin (n : Nat) (f : Fin n → Bool × Nat) : Bool × Nat :=
  let r := StoredForwardFinal.existsFin n (fun i => let a := f i; (!a.1,1+a.2))
  (!r.1,1+r.2)

theorem allFin_value (n : Nat) (f : Fin n → Bool × Nat) :
    (allFin n f).1=true ↔ ∀ i, (f i).1=true := by
  have hn (b : Bool) : (b=false ↔ ¬b=true) := by cases b <;> decide
  simp only [allFin,Bool.not_eq_true',hn,StoredForwardFinal.existsFin_value,not_exists,not_not]

def allBudget (n B : Nat) := 1+StoredForwardTableBuild.tabBudget n (1+B)

theorem allFin_bound (n B : Nat) (f : Fin n → Bool × Nat) (hf : ∀ i, (f i).2≤B) :
    (allFin n f).2 ≤ allBudget n B := by
  have h := StoredForwardFinal.existsFin_bound n (1+B)
    (fun i => let a := f i; (!a.1,1+a.2)) (fun i => Nat.add_le_add_left (hf i) 1)
  dsimp only at h
  exact Nat.add_le_add_left h 1

def cell (A : StoredOrdinaryDFABuild.Data) (q : Fin A.count) (i : Fin d) : Bool × Nat :=
  let t := StoredDFAAccess.step A q i
  let c := StoredPaddingDecode.less t.1 A.count
  (c.1,1+t.2+c.2)

theorem cell_bound (A : StoredOrdinaryDFABuild.Data) (q : Fin A.count) (i : Fin d) :
    (cell A q i).2 ≤ 2*A.count+d+3 := by
  have ht := StoredDFAAccess.step_bound A q i
  have hc := StoredPaddingDecode.less_bound (StoredDFAAccess.step A q i).1 A.count
  simp only [cell]
  omega

def check (A : StoredOrdinaryDFABuild.Data) : Bool × Nat :=
  let s := StoredPaddingDecode.less A.start A.count
  let t := allFin A.count (fun q => allFin d (cell A q))
  (s.1 && t.1,1+s.2+t.2)

theorem value (A : StoredOrdinaryDFABuild.Data) :
    (check (d := d) A).1=true ↔ StoredDFAProductCells.Valid (d := d) A := by
  simp only [check,Bool.and_eq_true,allFin_value,cell,StoredPaddingDecode.less_value]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.start,h.step⟩⟩

def budget (n d : Nat) := n+2+allBudget n (allBudget d (2*n+d+3))

theorem bound (A : StoredOrdinaryDFABuild.Data) :
    (check (d := d) A).2 ≤ budget A.count d := by
  have hs := StoredPaddingDecode.less_bound A.start A.count
  have ht := allFin_bound A.count (allBudget d (2*A.count+d+3))
    (fun q => allFin d (cell A q)) (fun q => allFin_bound d _ _ (cell_bound A q))
  simp only [check,budget]
  omega
end NSSE.StoredDFAValidity
