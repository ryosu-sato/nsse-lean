import NSSE.StoredForwardTableBuild

namespace NSSE.StoredForwardLookup
variable {n d : Nat}

def get {α : Type*} (fallback : α) : List α → Nat → α × Nat
  | [], _ => (fallback,1)
  | a::_, 0 => (a,1)
  | _::xs, k+1 => let r := get fallback xs k; (r.1,1+r.2)

theorem get_value {α : Type*} (fallback : α) (xs : List α) (k : Nat) :
    (get fallback xs k).1 = xs[k]?.getD fallback := by
  induction xs generalizing k with
  | nil => simp [get]
  | cons a xs ih => cases k <;> simp [get,ih]

theorem get_bound {α : Type*} (fallback : α) (xs : List α) (k : Nat) :
    (get fallback xs k).2 ≤ k+1 := by
  induction xs generalizing k with
  | nil => simp [get]
  | cons a xs ih => cases k with
    | zero => simp [get]
    | succ k => have h := ih k; simp only [get]; omega

theorem get_ofFn {α : Type*} (fallback : α) (f : Fin n → α) (i : Fin n) :
    (get fallback (List.ofFn f) i.val).1 = f i := by
  simp only [get_value,List.getElem?_ofFn]
  simp [i.isLt]

def two (xs : List (List Bool)) (x y : Nat) : Bool × Nat :=
  let a := get [] xs x
  let b := get false a.1 y
  (b.1,1+a.2+b.2)
def three (xs : List (List (List Bool))) (x i y : Nat) : Bool × Nat :=
  let a := get [] xs x
  let b := two a.1 i y
  (b.1,1+a.2+b.2)

theorem two_bound (xs : List (List Bool)) (x y : Nat) : (two xs x y).2 ≤ x+y+3 := by
  have h := get_bound [] xs x
  have h' := get_bound false (get [] xs x).1 y
  simp only [two]; omega

theorem three_bound (xs : List (List (List Bool))) (x i y : Nat) : (three xs x i y).2 ≤ x+i+y+5 := by
  have h := get_bound [] xs x
  have h' := two_bound (get [] xs x).1 i y
  simp only [three]; omega

theorem two_ofFn {m : Nat} (f : Fin n → Fin m → Bool) (x : Fin n) (y : Fin m) :
    (two (List.ofFn (fun x => List.ofFn (f x))) x.val y.val).1 = f x y := by
  simp only [two,get_ofFn]
theorem three_ofFn {m : Nat} (f : Fin n → Fin d → Fin m → Bool) (x : Fin n) (i : Fin d) (y : Fin m) :
    (three (List.ofFn (fun x => List.ofFn (fun i => List.ofFn (f x i)))) x.val i.val y.val).1 = f x i y := by
  simp only [three,get_ofFn,two_ofFn]

-- A semantic view only: callers must also charge the lookup counters.
def denote (D : StoredForwardTableBuild.Data n) : ForwardTableAutomaton.Tables n d :=
  ⟨D.queryLeft,D.queryRight,(fun x i y => (three D.upper x.val i.val y.val).1),
    (fun x i y => (three D.lower x.val i.val y.val).1),
    (fun x => (get false D.bot x.val).1),(fun x => (get false D.top x.val).1),
    (fun x y => (two D.le x.val y.val).1)⟩

theorem snapshot_value (D : ForwardTableAutomaton.Tables n d) :
    denote (StoredForwardTableBuild.snapshot D) = D := by
  cases D
  simp only [denote,StoredForwardTableBuild.snapshot,get_ofFn,two_ofFn,three_ofFn]

theorem value (Q : StoredTermAssembly.Query n d) :
    denote (StoredForwardTableBuild.build Q).1 = ConstraintForwardTables.tables (StoredForwardCells.query Q) := by
  rw [StoredForwardTableBuild.value,snapshot_value]

theorem relation_bound (D : StoredForwardTableBuild.Data n) (x y : Fin n) :
    (two D.le x.val y.val).2 ≤ 2*n+1 := by
  have h := two_bound D.le x.val y.val
  have hx := x.isLt; have hy := y.isLt
  omega

theorem move_bound (xs : List (List (List Bool))) (x : Fin n) (i : Fin d) (y : Fin n) :
    (three xs x.val i.val y.val).2 ≤ 2*n+d+2 := by
  have h := three_bound xs x.val i.val y.val
  have hx := x.isLt; have hy := y.isLt; have hi := i.isLt
  omega
end NSSE.StoredForwardLookup
