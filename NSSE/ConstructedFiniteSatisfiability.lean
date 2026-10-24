import NSSE.CountedFiniteModelConstruction
import NSSE.CountedFiniteSatisfiability

/-! Model expansion followed by actual validation. Labels/transitions count
as calls; their internal costs, lookup and bit costs are not yet included. -/
namespace NSSE.ConstructedFiniteSatisfiability
open FiniteSubtypeTrees SubtypeConstraints
variable {n d : Nat}

def build (φ : Constraints n d) : (Fin n → Tree d) × Nat :=
  let roots := List.ofFn (fun x => CountedFiniteModelConstruction.model φ x)
  ((fun x => (roots[x.val]'(by simp [roots])).1),
    1+(roots.map (fun r => 1+r.2)).sum)

theorem build_value (φ : Constraints n d) : (build φ).1 = FiniteSubtypeSmallModel.model φ := by
  funext x
  simp [build, CountedFiniteModelConstruction.model_value]

theorem build_bound (φ : Constraints n d) :
    (build φ).2 ≤ 1+n*(1+(4*d+3)^(2^n*2^n+1)) := by
  have hs := CountedFiniteTreeComparison.sum_bound
    (List.ofFn (fun x => CountedFiniteModelConstruction.model φ x)) (fun r => 1+r.2)
    (1+(4*d+3)^(2^n*2^n+1)) (by
      intro r hr
      obtain ⟨x,rfl⟩ := List.mem_ofFn.mp hr
      exact Nat.add_le_add_left (CountedFiniteModelConstruction.model_bound φ x) 1)
  simpa only [build, List.length_ofFn] using Nat.add_le_add_left hs 1

def decide (φ : Constraints n d) : Bool × Nat :=
  let b := build φ
  let c := CountedFiniteSatisfiability.check φ b.1
  (c.1,1+b.2+c.2)

theorem value (φ : Constraints n d) :
    (decide φ).1 = FiniteSubtypeDecision.decideSatisfiable φ := by
  simp only [decide, build_value, CountedFiniteSatisfiability.check_value]
  rfl

theorem correct (φ : Constraints n d) :
    (decide φ).1 = true ↔ Satisfiable (constructor d) φ := by
  rw [value, FiniteSubtypeDecision.decideSatisfiable_correct]

theorem bound (φ : Constraints n d) :
    (decide φ).2 ≤ 9+n*(1+(4*d+3)^(2^n*2^n+1))+
      CountedFiniteSatisfiability.literals φ*(1+(2*d+3)^(2^n*2^n+1)) := by
  have hb := build_bound φ
  have hc := CountedFiniteSatisfiability.bound φ
  simp only [decide, build_value]
  change 1+(build φ).2+(CountedFiniteSatisfiability.decide φ).2 ≤ _
  omega
end NSSE.ConstructedFiniteSatisfiability
