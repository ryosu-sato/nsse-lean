import NSSE.FiniteSubtypeDecision
import Mathlib.Tactic.Linarith

/-! Eager comparison: counts compared pairs and child-list cells.
Model construction and child-lookup implementation costs are excluded. -/
namespace NSSE.CountedFiniteTreeComparison
open FiniteSubtypeTrees FiniteTreeGrammar FiniteSubtypeSmallModel
variable {d : Nat}
def all (xs : List (Bool × Nat)) : Bool × Nat :=
  (xs.all Prod.fst, 1 + (xs.map (fun x => 1 + x.2)).sum)
def compare : Tree d → Tree d → Bool × Nat
  | .bot, _ => (true, 1)
  | .top, .top => (true, 1)
  | .top, .bot => (false, 1)
  | .top, .node _ => (false, 1)
  | .node _, .bot => (false, 1)
  | .node _, .top => (true, 1)
  | .node a, .node b =>
    let r := all ((List.finRange d).map (fun i => compare (a i) (b i)))
    (r.1, 1 + r.2)
theorem value (a b : Tree d) : (compare a b).1 = FiniteSubtypeDecision.leBool a b := by
  induction a generalizing b with
  | bot => rfl
  | top => cases b <;> rfl
  | node a ih =>
    cases b with
    | bot => rfl
    | top => rfl
    | node b => simp [compare, all, List.all_map, Function.comp_def, ih, FiniteSubtypeDecision.leBool]
theorem correct (a b : Tree d) : (compare a b).1 = true ↔ a ≤ b := by
  rw [value, FiniteSubtypeDecision.leBool_correct]
def budget (d : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => 2 + d * (1 + budget d k)
theorem budget_pos (k : Nat) : 1 ≤ budget d k := by
  cases k with
  | zero => simp [budget]
  | succ k => simp only [budget]; omega
theorem sum_bound {α : Type*} (xs : List α) (f : α → Nat) (B : Nat)
    (h : ∀ x ∈ xs, f x ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    omega
theorem node_bound (a b : Fin d → Tree d) (B : Nat)
    (h : ∀ i, (compare (a i) (b i)).2 ≤ B) :
    (compare (.node a) (.node b)).2 ≤ 2 + d * (1 + B) := by
  have hs := sum_bound (List.finRange d) (fun i => 1 + (compare (a i) (b i)).2)
    (1 + B) (fun i _ => Nat.add_le_add_left (h i) 1)
  simp only [List.length_finRange] at hs
  simpa only [compare, all, List.map_map, Function.comp_def, ← Nat.add_assoc] using Nat.add_le_add_left hs 2
/-- Applies to unsatisfiable inputs too; no stabilization premise. -/
theorem unfold_bound {S : Type*} (G : Grammar S d) (k : Nat) (s : S) (b : Tree d) :
    (compare (unfold G k s) b).2 ≤ budget d k := by
  induction k generalizing s b with
  | zero => simp [unfold, compare, budget]
  | succ k ih =>
    cases he : G.label s with
    | bot => simpa [unfold, he, compare] using (budget_pos (d := d) (k + 1))
    | top => cases b <;> simpa [unfold, he, compare] using (budget_pos (d := d) (k + 1))
    | node =>
      cases b with
      | bot => simpa [unfold, he, compare] using (budget_pos (d := d) (k + 1))
      | top => simpa [unfold, he, compare] using (budget_pos (d := d) (k + 1))
      | node b =>
        simpa [unfold, he, budget] using
          node_bound (fun i => unfold G k (G.next s i)) b (budget d k)
            (fun i => ih (G.next s i) (b i))
theorem budget_power (k : Nat) : budget d k ≤ (2 * d + 3) ^ (k + 1) := by
  induction k with
  | zero => simp [budget]
  | succ k ih =>
    have hp : 1 ≤ (2 * d + 3) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    rw [budget, pow_succ]
    have hm := Nat.mul_le_mul_left d ih
    nlinarith
theorem model_bound {n : Nat} (φ : SubtypeConstraints.Constraints n d)
    (x : Fin n) (b : Tree d) :
    (compare (model φ x) b).2 ≤ (2 * d + 3) ^ (2 ^ n * 2 ^ n + 1) := by
  have h := (unfold_bound (SubtypeShapeGrammar.grammar φ) (stateBound n)
    (SubtypeShapeGrammar.initial φ x) b).trans (budget_power (d := d) (stateBound n))
  simpa only [model, stateBound_eq] using h
theorem cost_symm (a b : Tree d) : (compare a b).2 = (compare b a).2 := by
  induction a generalizing b with
  | bot => cases b <;> rfl
  | top => cases b <;> rfl
  | node a ih =>
    cases b with
    | bot => rfl
    | top => rfl
    | node b => simp [compare, all, List.map_map, Function.comp_def, ih]
end NSSE.CountedFiniteTreeComparison
