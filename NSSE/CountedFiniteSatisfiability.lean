import NSSE.CountedFiniteTreeComparison

/-! Actual finite-model validation with eager comparison/list visit counts.
These counters exclude model construction and variable/child lookup costs. -/
namespace NSSE.CountedFiniteSatisfiability
open FiniteSubtypeTrees FiniteSubtypeSmallModel SubtypeConstraints
open CountedFiniteTreeComparison
variable {n d : Nat}

def check (φ : Constraints n d) (ρ : Fin n → Tree d) : Bool × Nat :=
  let u := all (φ.upper.map (fun a => compare (ρ a.1) (.node (fun i => ρ (a.2 i)))))
  let l := all (φ.lower.map (fun a => compare (.node (fun i => ρ (a.2 i))) (ρ a.1)))
  let b := all (φ.bot.map (fun x => compare (ρ x) .bot))
  let t := all (φ.top.map (fun x => compare .top (ρ x)))
  (u.1 && l.1 && b.1 && t.1, 3 + u.2 + l.2 + b.2 + t.2)

def decide (φ : Constraints n d) : Bool × Nat := check φ (model φ)

theorem check_value (φ : Constraints n d) (ρ : Fin n → Tree d) :
    (check φ ρ).1 = FiniteSubtypeDecision.checkSolution φ ρ := by
  simp [check, all, List.all_map, Function.comp_def,
    CountedFiniteTreeComparison.value, FiniteSubtypeDecision.checkSolution]

theorem value (φ : Constraints n d) :
    (decide φ).1 = FiniteSubtypeDecision.decideSatisfiable φ := check_value φ _

theorem correct (φ : Constraints n d) :
    (decide φ).1 = true ↔ Satisfiable (constructor d) φ := by
  rw [value, FiniteSubtypeDecision.decideSatisfiable_correct]

def literals (φ : Constraints n d) : Nat :=
  φ.upper.length + φ.lower.length + φ.bot.length + φ.top.length

theorem all_bound {α : Type*} (xs : List α) (f : α → Bool × Nat) (B : Nat)
    (h : ∀ x ∈ xs, (f x).2 ≤ B) :
    (all (xs.map f)).2 ≤ 1 + xs.length * (1 + B) := by
  have hs := sum_bound xs (fun x => 1 + (f x).2) (1 + B)
    (fun x hx => Nat.add_le_add_left (h x hx) 1)
  simpa only [all, List.map_map, Function.comp_def] using Nat.add_le_add_left hs 1

/-- A concrete upper bound for the validation counter on every input. -/
theorem bound (φ : Constraints n d) :
    (decide φ).2 ≤ 7 + literals φ * (1 + (2 * d + 3) ^ (2 ^ n * 2 ^ n + 1)) := by
  let B := (2 * d + 3) ^ (2 ^ n * 2 ^ n + 1)
  have hu := all_bound φ.upper
    (fun a => compare (model φ a.1) (.node (fun i => model φ (a.2 i)))) B
    (fun a _ => model_bound φ a.1 _)
  have hl := all_bound φ.lower
    (fun a => compare (.node (fun i => model φ (a.2 i))) (model φ a.1)) B
    (fun a _ => by rw [cost_symm]; exact model_bound φ a.1 _)
  have hb := all_bound φ.bot (fun x => compare (model φ x) .bot) B
    (fun x _ => model_bound φ x _)
  have ht := all_bound φ.top (fun x => compare .top (model φ x)) B
    (fun x _ => by rw [cost_symm]; exact model_bound φ x _)
  change 3 + _ + _ + _ + _ ≤ _
  dsimp only [literals]
  change _ ≤ 7 + (φ.upper.length + φ.lower.length + φ.bot.length + φ.top.length) * (1 + B)
  nlinarith
end NSSE.CountedFiniteSatisfiability
