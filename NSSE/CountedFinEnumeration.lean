import NSSE.CountedListConstruction

/-! Explicit finite index enumeration by recursive list construction.
Fin.succ is a unary successor; proof fields are erased. -/
namespace NSSE.CountedFinEnumeration
open CountedListConstruction

def enumerate : (n : Nat) → List (Fin n) × Nat
  | 0 => ([],1)
  | n+1 =>
    let r := enumerate n
    let s := map (fun i => (i.succ,1)) r.1
    (0::s.1,2+r.2+s.2)

theorem value (n : Nat) : (enumerate n).1 = List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [enumerate, map_value, ih, List.finRange_succ_eq_map]

theorem bound (n : Nat) : (enumerate n).2 ≤ (n+1)^2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := map_bound (fun i : Fin n => (i.succ,1)) (enumerate n).1 1 (fun _ _ => le_rfl)
    rw [value, List.length_finRange] at h
    simp only [enumerate, value]
    nlinarith

def tabulate {α : Type*} (n : Nat) (f : Fin n → α × Nat) : List α × Nat :=
  let r := enumerate n
  let s := map f r.1
  (s.1,1+r.2+s.2)

theorem tabulate_value {α : Type*} (n : Nat) (f : Fin n → α × Nat) :
    (tabulate n f).1 = List.ofFn (fun i => (f i).1) := by
  simp only [tabulate, map_value, value]
  apply List.ext_getElem <;> simp

theorem tabulate_bound {α : Type*} (n : Nat) (f : Fin n → α × Nat) (B : Nat)
    (h : ∀ i, (f i).2 ≤ B) : (tabulate n f).2 ≤ 2+(n+1)^2+n*(1+B) := by
  have hr := bound n
  have hs := map_bound f (enumerate n).1 B (fun i _ => h i)
  rw [value, List.length_finRange] at hs
  simp only [tabulate, value]; omega
end NSSE.CountedFinEnumeration
