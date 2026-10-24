import NSSE.CountedShapeLabel

/-! Counted initial state construction from actual support queries.
No set membership oracle is required to build these lists. -/
namespace NSSE.CountedShapeInitial
open SubtypeConstraints SubtypeShapeGrammar
variable {n d : Nat}

def select {α : Type*} (f : α → Bool × Nat) : List α → List α × Nat
  | [] => ([],1)
  | x::xs =>
    let a := f x
    let b := select f xs
    ((if a.1 then x::b.1 else b.1),2+a.2+b.2)

theorem select_value {α : Type*} (f : α → Bool × Nat) (xs : List α) :
    (select f xs).1 = xs.filter (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [select, List.filter_cons, ih]

theorem select_length {α : Type*} (f : α → Bool × Nat) (xs : List α) :
    (select f xs).1.length ≤ xs.length := by
  rw [select_value]
  exact List.length_filter_le _ _

theorem select_bound {α : Type*} (f : α → Bool × Nat) (xs : List α)
    (B : Nat) (h : ∀ x ∈ xs, (f x).2 ≤ B) :
    (select f xs).2 ≤ 1+xs.length*(2+B) := by
  induction xs with
  | nil => simp [select]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [select, List.length_cons]
    nlinarith

def down (φ : Constraints n d) (x : Fin n) : List (Fin n) × Nat :=
  select (fun z => CountedSubtypeSupport.query φ z x) (List.finRange n)

def up (φ : Constraints n d) (x : Fin n) : List (Fin n) × Nat :=
  select (fun z => CountedSubtypeSupport.query φ x z) (List.finRange n)

theorem down_value (φ : Constraints n d) (x : Fin n) :
    (down φ x).1.toFinset = SubtypeShapeGrammar.down φ x := by
  ext z
  simp [down, select_value, CountedSubtypeSupport.correct]

theorem up_value (φ : Constraints n d) (x : Fin n) :
    (up φ x).1.toFinset = SubtypeShapeGrammar.up φ x := by
  ext z
  simp [up, select_value, CountedSubtypeSupport.correct]

theorem down_length (φ : Constraints n d) (x : Fin n) : (down φ x).1.length ≤ n := by
  simpa only [List.length_finRange] using
    select_length (fun z => CountedSubtypeSupport.query φ z x) (List.finRange n)

theorem up_length (φ : Constraints n d) (x : Fin n) : (up φ x).1.length ≤ n := by
  simpa only [List.length_finRange] using
    select_length (fun z => CountedSubtypeSupport.query φ x z) (List.finRange n)

theorem down_bound (φ : Constraints n d) (x : Fin n) :
    (down φ x).2 ≤ 1+n*(2+CountedSubtypeSupport.queryBudget φ) := by
  simpa only [down, List.length_finRange] using
    select_bound (fun z => CountedSubtypeSupport.query φ z x) (List.finRange n)
      (CountedSubtypeSupport.queryBudget φ) (fun z _ => CountedSubtypeSupport.bound φ z x)

theorem up_bound (φ : Constraints n d) (x : Fin n) :
    (up φ x).2 ≤ 1+n*(2+CountedSubtypeSupport.queryBudget φ) := by
  simpa only [up, List.length_finRange] using
    select_bound (fun z => CountedSubtypeSupport.query φ x z) (List.finRange n)
      (CountedSubtypeSupport.queryBudget φ) (fun z _ => CountedSubtypeSupport.bound φ x z)

def initial (φ : Constraints n d) (x : Fin n) : (List (Fin n) × List (Fin n)) × Nat :=
  let a := down φ x
  let b := up φ x
  ((a.1,b.1),1+a.2+b.2)

theorem initial_value (φ : Constraints n d) (x : Fin n) :
    ((initial φ x).1.1.toFinset,(initial φ x).1.2.toFinset) =
      SubtypeShapeGrammar.initial φ x := by
  simp only [initial, down_value, up_value, SubtypeShapeGrammar.initial]

theorem initial_bound (φ : Constraints n d) (x : Fin n) :
    (initial φ x).2 ≤ 3+2*n*(2+CountedSubtypeSupport.queryBudget φ) := by
  have hd := down_bound φ x
  have hu := up_bound φ x
  simp only [initial]
  nlinarith
end NSSE.CountedShapeInitial
