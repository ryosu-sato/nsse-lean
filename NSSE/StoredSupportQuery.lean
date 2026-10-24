import NSSE.StoredSupportRules
import NSSE.InitializedHornEvaluation

/-! Support evaluation on stored flat inputs. Child traversal is included;
bit representation, counter arithmetic and concrete allocation remain open. -/
namespace NSSE.StoredSupportQuery
open StoredSubtypeInput
variable {n d : Nat}

def program (I : Input n d) : MaterializedHornProgram.Program × Nat :=
  let c := CountedSupportRule.mul n n
  let t := CountedSupportTerminals.table n
  let r := StoredSupportRules.rules I
  (⟨c.1,t.1,r.1⟩,1+c.2+t.2+r.2)

theorem program_value (I : Input n d) :
    (program I).1 = MaterializedHornProgram.materialize (FiniteSubtypeSupport.compiler I.denote) := by
  simp only [program, CountedSupportRule.mul_value, CountedSupportTerminals.table_value,
    StoredSupportRules.value, MaterializedHornProgram.materialize, FiniteSubtypeSupport.compiler]

def programBudget (I : Input n d) :=
  4+n*(n+2)+(n*n+1)^2+n*n*(1+CountedSupportTerminals.cellBudget n)+StoredSupportRules.budget I

theorem program_bound (I : Input n d) : (program I).2 ≤ programBudget I := by
  have ht := CountedSupportTerminals.table_bound n
  have hr := StoredSupportRules.bound I
  simp only [program, CountedSupportRule.mul_cost, programBudget]
  omega

def query (I : Input n d) (x y : Fin n) : Bool × Nat :=
  let p := program I
  let i := CountedSupportRule.pair x y
  let r := InitializedHornEvaluation.decide p.1 i.1
  (r.1,1+p.2+i.2+r.2)

theorem value (I : Input n d) (x y : Fin n) :
    (query I x y).1 = FiniteSubtypeSupport.table I.denote x y := by
  simp only [query, program_value, CountedSupportRule.pair_value,
    InitializedHornEvaluation.value, CountedHornEvaluation.materialize_value]
  rfl

theorem correct (I : Input n d) (x y : Fin n) :
    (query I x y).1 = true ↔ SubtypeConstraints.Support I.denote x y := by
  rw [value, FiniteSubtypeSupport.table_correct]

def budget (I : Input n d) :=
  3+programBudget I+CountedSupportRule.pairBudget n+
    CountedSubtypeSupport.queryBudget I.denote+n*n

theorem bound (I : Input n d) (x y : Fin n) : (query I x y).2 ≤ budget I := by
  have hp := program_bound I
  have hi := CountedSupportRule.pair_bound x y
  have hr := CountedSubtypeSupport.bound I.denote x y
  simp only [query, InitializedHornEvaluation.cost, program_value, CountedSupportRule.pair_value]
  change 1+(program I).2+(CountedSupportRule.pair x y).2+
    ((CountedSubtypeSupport.query I.denote x y).2+n*n+2) ≤ _
  dsimp only [budget]
  omega
end NSSE.StoredSupportQuery
