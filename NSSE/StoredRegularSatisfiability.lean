import NSSE.BinarySupportSize

namespace NSSE.StoredRegularSatisfiability
open StoredSubtypeInput

/-- Eager recursive traversal, counting the predicate and list operations. -/
def any {α : Type*} (f : α → Bool × Nat) : List α → Bool × Nat
  | [] => (false,1)
  | x::xs => let a := f x; let b := any f xs; (a.1 || b.1,1+a.2+b.2)

theorem any_value {α : Type*} (f : α → Bool × Nat) (xs : List α) :
    (any f xs).1 = xs.any (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((f x).1 || (any f xs).1) = _
    rw [ih]
    rfl

theorem any_bound {α : Type*} (f : α → Bool × Nat) (xs : List α) (B : Nat)
    (h : ∀ x ∈ xs, (f x).2 ≤ B) : (any f xs).2 ≤ 1+xs.length*(1+B) := by
  induction xs with
  | nil => simp [any]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [any,List.length_cons]
    nlinarith

def pairs {α β : Type*} (xs : List α) (ys : List β) (f : α → β → Bool × Nat) :=
  any (fun x => any (f x) ys) xs

theorem pairs_value {α β : Type*} (xs : List α) (ys : List β) (f : α → β → Bool × Nat) :
    (pairs xs ys f).1 = xs.any (fun x => ys.any (fun y => (f x y).1)) := by
  simp only [pairs,any_value]

theorem pairs_bound {α β : Type*} (xs : List α) (ys : List β) (f : α → β → Bool × Nat)
    (B : Nat) (h : ∀ x y, (f x y).2 ≤ B) :
    (pairs xs ys f).2 ≤ 1+xs.length*(2+ys.length*(1+B)) := by
  have hh := any_bound (fun x => any (f x) ys) xs (1+ys.length*(1+B))
    (fun x _ => any_bound (f x) ys B (fun y _ => h x y))
  simpa only [pairs,← Nat.add_assoc] using hh

variable {n d : Nat}
def decide (I : Input n d) : Bool × Nat :=
  let a := pairs I.top I.bot (fun x y => StoredSupportQuery.query I x y)
  let b := pairs I.top I.upper (fun x y => StoredSupportQuery.query I x y.head)
  let c := pairs I.lower I.bot (fun x y => StoredSupportQuery.query I x.head y)
  (!(a.1 || b.1 || c.1),3+a.2+b.2+c.2)

theorem value (I : Input n d) : (decide I).1 = RegularSubtypeModel.decideSatisfiable I.denote := by
  simp only [decide,pairs_value,StoredSupportQuery.value,RegularSubtypeModel.decideSatisfiable,
    SubtypeLabelClashes.labelClashBool,Input.denote,List.any_map,Function.comp_def,Bound.denote]

theorem correct (I : Input n d) :
    (decide I).1 = true ↔ SubtypeConstraints.Satisfiable (AbsorbingSubtypeTrees.constructor d) I.denote := by
  rw [value,RegularSubtypeModel.decideSatisfiable_correct]

theorem regular_correct (I : Input n d) :
    (decide I).1 = true ↔ RegularSubtypeTrees.RegularSatisfiable I.denote := by
  rw [value,RegularSubtypeModel.decideRegularSatisfiable_correct]

def budget (n d m : Nat) := 6+3*m*(2+m*(1+BinarySupportSize.solverBudget n d m))

theorem bound (I : Input n d) (m : Nat) (hu : I.upper.length ≤ m) (hl : I.lower.length ≤ m)
    (hb : I.bot.length ≤ m) (ht : I.top.length ≤ m) : (decide I).2 ≤ budget n d m := by
  let B := BinarySupportSize.solverBudget n d m
  have hq (x y : Fin n) : (StoredSupportQuery.query I x y).2 ≤ B :=
    (StoredSupportQuery.bound I x y).trans (BinarySupportSize.solver_bound I m hu hl)
  have ha := pairs_bound I.top I.bot (fun x y => StoredSupportQuery.query I x y) B hq
  have hc := pairs_bound I.top I.upper (fun x y => StoredSupportQuery.query I x y.head) B (fun x y => hq x y.head)
  have he := pairs_bound I.lower I.bot (fun x y => StoredSupportQuery.query I x.head y) B (fun x y => hq x.head y)
  have h1 : I.top.length*(2+I.bot.length*(1+B)) ≤ m*(2+m*(1+B)) := by gcongr
  have h2 : I.top.length*(2+I.upper.length*(1+B)) ≤ m*(2+m*(1+B)) := by gcongr
  have h3 : I.lower.length*(2+I.bot.length*(1+B)) ≤ m*(2+m*(1+B)) := by gcongr
  change 3+_+_+_ ≤ 6+3*m*(2+m*(1+B))
  nlinarith

theorem budget_mono (n d m N D : Nat) (hn : n ≤ N) (hd : d ≤ D) :
    budget n d m ≤ budget N D m := by
  have h := BinarySupportSize.solver_mono n d m N D hn hd
  dsimp only [budget]
  gcongr
end NSSE.StoredRegularSatisfiability
