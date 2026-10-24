import NSSE.ExactReachabilityTable
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! # Polynomial formula-tree growth of exact reachability tables

`nodes` counts the actual primitive formula constructors, with derived
Boolean connectives expanded. Term and identifier encoding costs are
separate; this is not by itself a machine running-time theorem.
-/

namespace NSSE.ExactReachabilitySize

open FirstOrder FirstOrder.Language ExactReachabilityTable SymbolicReachability

universe u v w z
variable {L : FirstOrder.Language.{u,v}} {P : Type w}

def nodes {α : Type z} : {k : Nat} → L.BoundedFormula α k → Nat
  | _, .falsum => 1
  | _, .equal _ _ => 1
  | _, .rel _ _ => 1
  | _, .imp f g => 1 + nodes f + nodes g
  | _, .all f => 1 + nodes f

@[simp] theorem nodes_not {α : Type z} {k : Nat} (f : L.BoundedFormula α k) :
    nodes f.not = nodes f + 2 := by simp [BoundedFormula.not, nodes]; omega

@[simp] theorem nodes_inf {α : Type z} {k : Nat} (f g : L.BoundedFormula α k) :
    nodes (f ⊓ g) = 5 + nodes f + nodes g := by
  change nodes ((f.imp g.not).not) = _
  simp [nodes]; omega

@[simp] theorem nodes_sup {α : Type z} {k : Nat} (f g : L.BoundedFormula α k) :
    nodes (f ⊔ g) = 3 + nodes f + nodes g := by
  change nodes (f.not.imp g) = _
  simp [nodes]; omega

@[simp] theorem nodes_iff {α : Type z} {k : Nat} (f g : L.BoundedFormula α k) :
    nodes (f.iff g) = 7 + 2*nodes f + 2*nodes g := by
  simp [BoundedFormula.iff, nodes]; omega

@[simp] theorem nodes_bdRelabel {α β : Type*} {k m : Nat}
    (f : L.BoundedFormula α k) (g : α → β ⊕ Fin m) : nodes (f.relabel g) = nodes f := by
  induction f with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp _ _ ih₁ ih₂ => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, nodes] at *; omega
  | all _ ih => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, nodes] at *; omega

@[simp] theorem nodes_relabel {α β : Type*} (f : L.Formula α) (g : α → β) :
    nodes (f.relabel g) = nodes f := nodes_bdRelabel _ _

theorem nodes_fold_inf (fs : List (L.Formula P)) :
    nodes (fs.foldr (· ⊓ ·) ⊤) = 3 + (fs.map (fun f => 5 + nodes f)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [List.foldr_cons, nodes_inf, ih, List.map_cons, List.sum_cons]; omega

theorem nodes_fold_sup (fs : List (L.Formula P)) :
    nodes (fs.foldr (· ⊔ ·) ⊥) = 1 + (fs.map (fun f => 3 + nodes f)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [List.foldr_cons, nodes_sup, ih, List.map_cons, List.sum_cons]; omega

@[simp] theorem nodes_every (m : Nat) (f : Fin m → L.Formula P) :
    nodes (every m f) = 3 + ∑ i, (5 + nodes (f i)) := by
  simp [every, nodes_fold_inf, List.map_map, List.finRange, List.map_ofFn, List.sum_ofFn]

@[simp] theorem nodes_any (m : Nat) (f : Fin m → L.Formula P) :
    nodes (any m f) = 1 + ∑ i, (3 + nodes (f i)) := by
  simp [any, nodes_fold_sup, List.map_map, List.finRange, List.map_ofFn, List.sum_ofFn]

@[simp] theorem nodes_bit {n T : Nat} (one : P) (t : Fin (T+1)) (q : Fin n) :
    nodes (bit (L := L) one t q) = 1 := rfl

theorem nodes_matrix {n : Nat} (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P) (T : Nat) :
    nodes (matrix initial step one T) =
      11 + (∑ q, (14 + 2*nodes (initial q))) +
        ∑ t : Fin T, (8 + ∑ q, (16 + 2*∑ r, (9 + nodes (step t r q)))) := by
  simp only [matrix, nodes_inf, nodes_every, nodes_iff, nodes_bit, nodes_relabel, nodes_any]
  have h (a : Nat) : 5+(7+2*1+2*a) = 14+2*a := by omega
  have h' (a : Nat) : 5+(7+2*1+2*(1+a)) = 16+2*a := by omega
  simp only [h, h']
  norm_num
  ring_nf

theorem nodes_output {n : Nat} (final : Fin n → L.Formula P) (one : P) (T : Nat) :
    nodes (output final one T) = 1 + ∑ q, (9 + nodes (final q)) := by
  simp only [output, nodes_any, nodes_inf, nodes_bit, nodes_relabel]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  omega

theorem nodes_signed_le (positive : Bool) (f : L.Formula P) :
    nodes (signed positive f) ≤ nodes f + 2 := by
  cases positive <;> simp [signed]

@[simp] theorem nodes_exs {α : Type*} {k : Nat} (f : L.BoundedFormula α k) :
    nodes f.exs = nodes f + 5*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFormula.exs, ih]
    change nodes ((f.not).all.not) + 5*k = _
    simp only [nodes_not, nodes]
    omega

@[simp] theorem nodes_closeColumn {k : Nat} (f : L.Formula (P ⊕ Fin k)) :
    nodes (closeColumn f) = nodes f + 5*k := by
  rw [closeColumn, nodes_exs, nodes_bdRelabel, Nat.add_zero]

theorem nodes_compile_le {n G : Nat} (initial final : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P) (T : Nat) (positive : Bool)
    (hi : ∀ q, nodes (initial q) ≤ G) (hf : ∀ q, nodes (final q) ≤ G)
    (hs : ∀ t < T, ∀ q r, nodes (step t q r) ≤ G) :
    nodes (compile initial final step one T positive) ≤
      19 + n*(14+2*G) + T*(8+n*(16+2*n*(9+G))) + n*(9+G) + 5*((T+1)*n) := by
  have sum_le {m : Nat} (f : Fin m → Nat) (b : Nat) (h : ∀ i, f i ≤ b) :
      (∑ i, f i) ≤ m*b := by
    calc
      _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp
  have hi' := sum_le (fun q => 14+2*nodes (initial q)) (14+2*G)
    (fun q => Nat.add_le_add_left (Nat.mul_le_mul_left 2 (hi q)) 14)
  have hf' := sum_le (fun q => 9+nodes (final q)) (9+G)
    (fun q => Nat.add_le_add_left (hf q) 9)
  have hs' (t : Fin T) (q : Fin n) : (∑ r, (9+nodes (step t r q))) ≤ n*(9+G) :=
    sum_le _ _ (fun r => Nat.add_le_add_left (hs t t.isLt r q) 9)
  have hq (t : Fin T) : (∑ q, (16+2*∑ r, (9+nodes (step t r q)))) ≤ n*(16+2*n*(9+G)) := by
    apply sum_le
    intro q
    have h := Nat.mul_le_mul_left 2 (hs' t q)
    simpa only [Nat.mul_assoc] using Nat.add_le_add_left h 16
  have ht := sum_le (fun t : Fin T => 8+∑ q, (16+2*∑ r, (9+nodes (step t r q))))
    (8+n*(16+2*n*(9+G))) (fun t => Nat.add_le_add_left (hq t) 8)
  dsimp only at hi' hf' ht
  have hp := nodes_signed_le positive (output final one T)
  rw [nodes_output] at hp
  simp only [compile, nodes_closeColumn, nodes_inf, nodes_matrix]
  omega

end NSSE.ExactReachabilitySize
