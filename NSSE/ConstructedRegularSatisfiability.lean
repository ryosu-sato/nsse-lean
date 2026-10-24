import NSSE.InitializedSupportQuery

/-! Regular/arbitrary SAT with constructed, initialized support queries.
Input child access, counter arithmetic and concrete allocation/bit costs
remain excluded. Every pair query constructs its own support program. -/
namespace NSSE.ConstructedRegularSatisfiability
open SubtypeConstraints CountedRegularSatisfiability
variable {n d : Nat}

def decide (φ : Constraints n d) : Bool × Nat :=
  let a := testPairs φ.top φ.bot (fun x y => InitializedSupportQuery.query φ x y)
  let b := testPairs φ.top φ.upper (fun x y => InitializedSupportQuery.query φ x y.1)
  let c := testPairs φ.lower φ.bot (fun x y => InitializedSupportQuery.query φ x.1 y)
  (!(a.1 || b.1 || c.1),3+a.2+b.2+c.2)

theorem value (φ : Constraints n d) :
    (decide φ).1 = RegularSubtypeModel.decideSatisfiable φ := by
  simp only [decide, pairs_value, InitializedSupportQuery.value,
    RegularSubtypeModel.decideSatisfiable, SubtypeLabelClashes.labelClashBool]

theorem correct (φ : Constraints n d) :
    (decide φ).1 = true ↔ Satisfiable (AbsorbingSubtypeTrees.constructor d) φ := by
  rw [value, RegularSubtypeModel.decideSatisfiable_correct]

theorem regular_correct (φ : Constraints n d) :
    (decide φ).1 = true ↔ RegularSubtypeTrees.RegularSatisfiable φ := by
  rw [value, RegularSubtypeModel.decideRegularSatisfiable_correct]

def budget (φ : Constraints n d) :=
  let m := CountedFiniteSatisfiability.literals φ
  6+3*m*(2+m*(1+InitializedSupportQuery.budget φ))

theorem bound (φ : Constraints n d) : (decide φ).2 ≤ budget φ := by
  let B := InitializedSupportQuery.budget φ
  let m := CountedFiniteSatisfiability.literals φ
  have htop : φ.top.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have hbot : φ.bot.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have hu : φ.upper.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have hl : φ.lower.length ≤ m := by dsimp [m, CountedFiniteSatisfiability.literals]; omega
  have ha := pairs_bound φ.top φ.bot (fun x y => InitializedSupportQuery.query φ x y)
    B (fun x y => InitializedSupportQuery.bound φ x y)
  have hb := pairs_bound φ.top φ.upper (fun x y => InitializedSupportQuery.query φ x y.1)
    B (fun x y => InitializedSupportQuery.bound φ x y.1)
  have hc := pairs_bound φ.lower φ.bot (fun x y => InitializedSupportQuery.query φ x.1 y)
    B (fun x y => InitializedSupportQuery.bound φ x.1 y)
  have h1 : φ.top.length*(2+φ.bot.length*(1+B)) ≤ m*(2+m*(1+B)) := by gcongr
  have h2 : φ.top.length*(2+φ.upper.length*(1+B)) ≤ m*(2+m*(1+B)) := by gcongr
  have h3 : φ.lower.length*(2+φ.bot.length*(1+B)) ≤ m*(2+m*(1+B)) := by gcongr
  change 3+_+_+_ ≤ 6+3*m*(2+m*(1+B))
  nlinarith
end NSSE.ConstructedRegularSatisfiability
