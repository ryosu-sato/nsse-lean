import NSSE.CountedSupportRule

/-! Recursive list construction counters for materialization pipelines. -/
namespace NSSE.CountedListConstruction

def append {α : Type*} : List α → List α → List α × Nat
  | [],ys => (ys,1)
  | x::xs,ys => let r := append xs ys; (x::r.1,1+r.2)
theorem append_value {α : Type*} (xs ys : List α) : (append xs ys).1 = xs++ys := by
  induction xs <;> simp [append, *]
theorem append_cost {α : Type*} (xs ys : List α) : (append xs ys).2 = xs.length+1 := by
  induction xs <;> simp [append, *, Nat.add_comm]

def map {α β : Type*} (f : α → β × Nat) : List α → List β × Nat
  | [] => ([],1)
  | x::xs => let a := f x; let b := map f xs; (a.1::b.1,1+a.2+b.2)
theorem map_value {α β : Type*} (f : α → β × Nat) (xs : List α) :
    (map f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs <;> simp [map, *]
theorem map_bound {α β : Type*} (f : α → β × Nat) (xs : List α) (B : Nat)
    (h : ∀ x ∈ xs, (f x).2 ≤ B) : (map f xs).2 ≤ 1+xs.length*(1+B) := by
  induction xs with
  | nil => simp [map]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [map, List.length_cons]; nlinarith

def flatMap {α β : Type*} (f : α → List β × Nat) : List α → List β × Nat
  | [] => ([],1)
  | x::xs =>
    let a := f x
    let b := flatMap f xs
    let c := append a.1 b.1
    (c.1,1+a.2+b.2+c.2)
theorem flatMap_value {α β : Type*} (f : α → List β × Nat) (xs : List α) :
    (flatMap f xs).1 = xs.flatMap (fun x => (f x).1) := by
  induction xs <;> simp [flatMap, append_value, *]
theorem flatMap_bound {α β : Type*} (f : α → List β × Nat) (xs : List α) (B L : Nat)
    (hb : ∀ x ∈ xs, (f x).2 ≤ B) (hl : ∀ x ∈ xs, (f x).1.length ≤ L) :
    (flatMap f xs).2 ≤ 1+xs.length*(2+B+L) := by
  induction xs with
  | nil => simp [flatMap]
  | cons x xs ih =>
    have hc := hb x (by simp)
    have hn := hl x (by simp)
    have ht := ih (fun y hy => hb y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
    simp only [flatMap, append_cost, List.length_cons]; nlinarith
def product3 {α β γ δ : Type*} (f : α → β → γ → δ × Nat)
    (xs : List α) (ys : List β) (zs : List γ) : List δ × Nat :=
  flatMap (fun x => flatMap (fun y => map (f x y) zs) ys) xs

theorem product3_value {α β γ δ : Type*} (f : α → β → γ → δ × Nat)
    (xs : List α) (ys : List β) (zs : List γ) :
    (product3 f xs ys zs).1 = xs.flatMap (fun x => ys.flatMap (fun y => zs.map (fun z => (f x y z).1))) := by
  simp only [product3, flatMap_value, map_value]

def productBudget (x y z B : Nat) := 1+x*(2+(1+y*(2+(1+z*(1+B))+z))+y*z)

theorem product3_bound {α β γ δ : Type*} (f : α → β → γ → δ × Nat)
    (xs : List α) (ys : List β) (zs : List γ) (B : Nat)
    (h : ∀ x y z, (f x y z).2 ≤ B) :
    (product3 f xs ys zs).2 ≤ productBudget xs.length ys.length zs.length B := by
  have hr (x : α) (y : β) := map_bound (f x y) zs B (fun z _ => h x y z)
  have hp (x : α) := flatMap_bound (fun y => map (f x y) zs) ys
    (1+zs.length*(1+B)) zs.length (fun y _ => hr x y)
    (fun y _ => by simp [map_value])
  exact flatMap_bound _ xs _ (ys.length*zs.length) (fun x _ => hp x) (fun x _ => by
    simp [flatMap_value, map_value, List.length_flatMap, List.map_const',
      List.sum_replicate, smul_eq_mul])
end NSSE.CountedListConstruction
