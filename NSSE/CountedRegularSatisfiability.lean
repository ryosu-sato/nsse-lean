import NSSE.CountedSubtypeSupport
import NSSE.CountedFiniteSatisfiability
import NSSE.RegularSubtypeModel

/-! Eager label-clash testing, including a fresh counted support saturation
for each queried pair. Construction/materialization/bit costs are excluded. -/
namespace NSSE.CountedRegularSatisfiability
open SubtypeConstraints
variable {n d : Nat}

def any (xs : List (Bool × Nat)) : Bool × Nat :=
  (xs.any Prod.fst, 1+(xs.map (fun x => 1+x.2)).sum)

def testPairs {α β : Type*} (xs : List α) (ys : List β)
    (f : α → β → Bool × Nat) : Bool × Nat :=
  any (xs.map (fun x => any (ys.map (f x))))

theorem pairs_value {α β : Type*} (xs : List α) (ys : List β)
    (f : α → β → Bool × Nat) :
    (testPairs xs ys f).1 = xs.any (fun x => ys.any (fun y => (f x y).1)) := by
  simp [testPairs, any, List.any_map, Function.comp_def]

theorem any_bound {α : Type*} (xs : List α) (f : α → Bool × Nat) (B : Nat)
    (h : ∀ x ∈ xs, (f x).2 ≤ B) :
    (any (xs.map f)).2 ≤ 1+xs.length*(1+B) := by
  have hs := CountedFiniteTreeComparison.sum_bound xs (fun x => 1+(f x).2) (1+B)
    (fun x hx => Nat.add_le_add_left (h x hx) 1)
  simpa only [any, List.map_map, Function.comp_def] using Nat.add_le_add_left hs 1

theorem pairs_bound {α β : Type*} (xs : List α) (ys : List β)
    (f : α → β → Bool × Nat) (B : Nat) (h : ∀ x y, (f x y).2 ≤ B) :
    (testPairs xs ys f).2 ≤ 1+xs.length*(2+ys.length*(1+B)) := by
  have hh := any_bound xs (fun x => any (ys.map (f x))) (1+ys.length*(1+B))
    (fun x _ => any_bound ys (f x) B (fun y _ => h x y))
  simpa only [testPairs, ← Nat.add_assoc] using hh

def decide (φ : Constraints n d) : Bool × Nat :=
  let a := testPairs φ.top φ.bot (fun x y => CountedSubtypeSupport.query φ x y)
  let b := testPairs φ.top φ.upper (fun x y => CountedSubtypeSupport.query φ x y.1)
  let c := testPairs φ.lower φ.bot (fun x y => CountedSubtypeSupport.query φ x.1 y)
  (!(a.1 || b.1 || c.1),3+a.2+b.2+c.2)

theorem value (φ : Constraints n d) :
    (decide φ).1 = RegularSubtypeModel.decideSatisfiable φ := by
  simp only [decide, pairs_value, CountedSubtypeSupport.value,
    RegularSubtypeModel.decideSatisfiable, SubtypeLabelClashes.labelClashBool]

theorem correct (φ : Constraints n d) :
    (decide φ).1 = true ↔ Satisfiable (AbsorbingSubtypeTrees.constructor d) φ := by
  rw [value, RegularSubtypeModel.decideSatisfiable_correct]

theorem regular_correct (φ : Constraints n d) :
    (decide φ).1 = true ↔ RegularSubtypeTrees.RegularSatisfiable φ := by
  rw [value, RegularSubtypeModel.decideRegularSatisfiable_correct]

def budget (φ : Constraints n d) : Nat :=
  let B := CountedSubtypeSupport.queryBudget φ
  6+φ.top.length*(2+φ.bot.length*(1+B))+
    φ.top.length*(2+φ.upper.length*(1+B))+
    φ.lower.length*(2+φ.bot.length*(1+B))

theorem bound (φ : Constraints n d) : (decide φ).2 ≤ budget φ := by
  have ha := pairs_bound φ.top φ.bot (fun x y => CountedSubtypeSupport.query φ x y)
    (CountedSubtypeSupport.queryBudget φ) (fun x y => CountedSubtypeSupport.bound φ x y)
  have hb := pairs_bound φ.top φ.upper (fun x y => CountedSubtypeSupport.query φ x y.1)
    (CountedSubtypeSupport.queryBudget φ) (fun x y => CountedSubtypeSupport.bound φ x y.1)
  have hc := pairs_bound φ.lower φ.bot (fun x y => CountedSubtypeSupport.query φ x.1 y)
    (CountedSubtypeSupport.queryBudget φ) (fun x y => CountedSubtypeSupport.bound φ x.1 y)
  simp only [decide, budget]
  omega
def polynomial (n d m : Nat) : Nat :=
  let B := CountedHornEvaluationBound.budget (n*n) (n*n*n+m*m*d) 2
  6+3*m*(2+m*(1+B))

theorem polynomial_bound (φ : Constraints n d) :
    (decide φ).2 ≤ polynomial n d (CountedFiniteSatisfiability.literals φ) := by
  let m := CountedFiniteSatisfiability.literals φ
  have ht : φ.top.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have hb : φ.bot.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have hu : φ.upper.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have hl : φ.lower.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  let B := CountedHornEvaluationBound.budget (n*n) (n*n*n+m*m*d) 2
  have hB : CountedSubtypeSupport.queryBudget φ ≤ B := by
    dsimp [CountedSubtypeSupport.queryBudget, B, CountedHornEvaluationBound.budget,
      CountedHornEvaluationBound.cellBudget]
    gcongr
  have h1 : φ.top.length*(2+φ.bot.length*(1+CountedSubtypeSupport.queryBudget φ)) ≤
      m*(2+m*(1+B)) := by gcongr
  have h2 : φ.top.length*(2+φ.upper.length*(1+CountedSubtypeSupport.queryBudget φ)) ≤
      m*(2+m*(1+B)) := by gcongr
  have h3 : φ.lower.length*(2+φ.bot.length*(1+CountedSubtypeSupport.queryBudget φ)) ≤
      m*(2+m*(1+B)) := by gcongr
  apply (bound φ).trans
  change 6+_+_+_ ≤ 6+3*m*(2+m*(1+B))
  nlinarith
end NSSE.CountedRegularSatisfiability
