import NSSE.InitializedHornEvaluation
import NSSE.ConstructedSupportQuery

/-! Actual constructed support queries, now also charging initial masks. -/
namespace NSSE.InitializedSupportQuery
open SubtypeConstraints
variable {n d : Nat}

def query (φ : Constraints n d) (x y : Fin n) : Bool × Nat :=
  let p := ConstructedSupportQuery.program φ
  let i := CountedSupportRule.pair x y
  let r := InitializedHornEvaluation.decide p.1 i.1
  (r.1,1+p.2+i.2+r.2)

theorem value (φ : Constraints n d) (x y : Fin n) :
    (query φ x y).1 = FiniteSubtypeSupport.table φ x y := by
  simp only [query, InitializedHornEvaluation.value]
  exact ConstructedSupportQuery.value φ x y

theorem correct (φ : Constraints n d) (x y : Fin n) :
    (query φ x y).1 = true ↔ Support φ x y := by
  rw [value, FiniteSubtypeSupport.table_correct]

theorem cost (φ : Constraints n d) (x y : Fin n) :
    (query φ x y).2 = (ConstructedSupportQuery.query φ x y).2+n*n+2 := by
  simp only [query, InitializedHornEvaluation.cost, ConstructedSupportQuery.query]
  have hp : (ConstructedSupportQuery.program φ).1.count = n*n := by
    rw [ConstructedSupportQuery.program_value]; rfl
  rw [hp]
  omega

def budget (φ : Constraints n d) :=
  3+ConstructedSupportQuery.programBudget φ+CountedSupportRule.pairBudget n+
    CountedSubtypeSupport.queryBudget φ+n*n

theorem bound (φ : Constraints n d) (x y : Fin n) : (query φ x y).2 ≤ budget φ := by
  have h := ConstructedSupportQuery.bound φ x y
  rw [cost]
  dsimp only [budget]
  omega
end NSSE.InitializedSupportQuery
