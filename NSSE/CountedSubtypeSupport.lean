import NSSE.CountedHornEvaluationBound
import NSSE.FiniteSubtypeSupport

/-! Counted support queries compute actual Horn saturation. Terminal/rule
materialization and bit/index/allocation costs are not charged here. -/
namespace NSSE.CountedSubtypeSupport
open FiniteSubtypeSupport MaterializedHornProgram CountedHornEvaluationBound
variable {n d : Nat}

theorem trans_length (n : Nat) : (transRules n).length = n*n*n := by
  simp [transRules, List.length_flatMap, List.map_const', List.sum_replicate,
    smul_eq_mul, Nat.mul_assoc]
theorem decomp_length (φ : SubtypeConstraints.Constraints n d) :
    (decompRules φ).length = φ.lower.length*φ.upper.length*d := by
  simp [decompRules, List.length_flatMap, List.map_const', List.sum_replicate,
    smul_eq_mul, Nat.mul_assoc]
theorem rules_length (φ : SubtypeConstraints.Constraints n d) :
    (compiler φ).rules.length = n*n*n+φ.lower.length*φ.upper.length*d := by
  simp [compiler, trans_length, decomp_length]
theorem children_length (φ : SubtypeConstraints.Constraints n d)
    (r : HornRule) (h : r ∈ (compiler φ).rules) : r.children.length ≤ 2 := by
  rcases List.mem_append.mp h with ht | hd
  · obtain ⟨x,y,z,rfl⟩ := (mem_transRules _).mp ht
    simp [transRule]
  · obtain ⟨a,ha,b,hb,i,rfl⟩ := (mem_decompRules φ _).mp hd
    simp [decompRule]

def query (φ : SubtypeConstraints.Constraints n d) (x y : Fin n) : Bool × Nat :=
  CountedHornEvaluation.decide (materialize (compiler φ)) (pairId x y)

theorem value (φ : SubtypeConstraints.Constraints n d) (x y : Fin n) :
    (query φ x y).1 = table φ x y :=
  CountedHornEvaluation.materialize_value _ _

theorem correct (φ : SubtypeConstraints.Constraints n d) (x y : Fin n) :
    (query φ x y).1 = true ↔ SubtypeConstraints.Support φ x y := by
  rw [value, table_correct]

def queryBudget (φ : SubtypeConstraints.Constraints n d) : Nat :=
  budget (n*n) (n*n*n+φ.lower.length*φ.upper.length*d) 2

theorem bound (φ : SubtypeConstraints.Constraints n d) (x y : Fin n) :
    (query φ x y).2 ≤ queryBudget φ := by
  have ht : (materialize (compiler φ)).terminals.length ≤ (materialize (compiler φ)).count :=
    Nat.le_of_eq (ExplicitUnaryTableLanguage.tabulate_length _)
  have h := decide_bound (materialize (compiler φ)) (pairId x y) 2 ht
    (fun r hr => children_length φ r hr)
  change (query φ x y).2 ≤ budget (n*n) (compiler φ).rules.length 2 at h
  rw [rules_length] at h
  exact h
end NSSE.CountedSubtypeSupport
