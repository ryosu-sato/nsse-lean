import NSSE.CountedSupportTerminals
import NSSE.CountedSupportRules

/-! Support queries with actual enumeration, rule and terminal construction.
Input child lookup, initial-mask construction, bit/counter/allocation costs
are still excluded from this structural counter. -/
namespace NSSE.ConstructedSupportQuery
open SubtypeConstraints CountedListConstruction
variable {n d : Nat}

def rules (φ : Constraints n d) : List HornRule × Nat :=
  let ns := CountedFinEnumeration.enumerate n
  let ds := CountedFinEnumeration.enumerate d
  let a := product3 CountedSupportRule.trans ns.1 ns.1 ns.1
  let b := product3 CountedSupportRule.decomp φ.lower φ.upper ds.1
  let c := append a.1 b.1
  (c.1,2+ns.2+ds.2+a.2+b.2+c.2)

theorem rules_value (φ : Constraints n d) : (rules φ).1 = (FiniteSubtypeSupport.compiler φ).rules := by
  simp only [rules, CountedFinEnumeration.value, append_value, product3_value,
    CountedSupportRule.trans_value, CountedSupportRule.decomp_value,
    FiniteSubtypeSupport.compiler, FiniteSubtypeSupport.transRules, FiniteSubtypeSupport.decompRules]

def rulesBudget (φ : Constraints n d) :=
  4+(n+1)^2+(d+1)^2+CountedSupportRules.transBudget n+CountedSupportRules.decompBudget φ+n*n*n

theorem rules_bound (φ : Constraints n d) : (rules φ).2 ≤ rulesBudget φ := by
  have hn := CountedFinEnumeration.bound n
  have hd := CountedFinEnumeration.bound d
  have ht := CountedSupportRules.trans_bound n
  have he := CountedSupportRules.decomp_bound φ
  simp only [rules, CountedFinEnumeration.value, append_cost]
  change 2+_+_+(CountedSupportRules.trans n).2+(CountedSupportRules.decomp φ).2+
    ((CountedSupportRules.trans n).1.length+1) ≤ _
  rw [CountedSupportRules.trans_value, CountedSubtypeSupport.trans_length]
  dsimp only [rulesBudget]
  omega

def program (φ : Constraints n d) : MaterializedHornProgram.Program × Nat :=
  let c := CountedSupportRule.mul n n
  let t := CountedSupportTerminals.table n
  let r := rules φ
  (⟨c.1,t.1,r.1⟩,1+c.2+t.2+r.2)

theorem program_value (φ : Constraints n d) :
    (program φ).1 = MaterializedHornProgram.materialize (FiniteSubtypeSupport.compiler φ) := by
  simp only [program, CountedSupportRule.mul_value, CountedSupportTerminals.table_value,
    rules_value, MaterializedHornProgram.materialize, FiniteSubtypeSupport.compiler]

def programBudget (φ : Constraints n d) :=
  4+n*(n+2)+(n*n+1)^2+n*n*(1+CountedSupportTerminals.cellBudget n)+rulesBudget φ

theorem program_bound (φ : Constraints n d) : (program φ).2 ≤ programBudget φ := by
  have ht := CountedSupportTerminals.table_bound n
  have hr := rules_bound φ
  simp only [program, CountedSupportRule.mul_cost, programBudget]
  omega

def query (φ : Constraints n d) (x y : Fin n) : Bool × Nat :=
  let p := program φ
  let i := CountedSupportRule.pair x y
  let r := CountedHornEvaluation.decide p.1 i.1
  (r.1,1+p.2+i.2+r.2)

theorem value (φ : Constraints n d) (x y : Fin n) :
    (query φ x y).1 = FiniteSubtypeSupport.table φ x y := by
  simp only [query, program_value, CountedSupportRule.pair_value,
    CountedHornEvaluation.materialize_value]
  rfl

theorem correct (φ : Constraints n d) (x y : Fin n) :
    (query φ x y).1 = true ↔ Support φ x y := by rw [value, FiniteSubtypeSupport.table_correct]

theorem bound (φ : Constraints n d) (x y : Fin n) :
    (query φ x y).2 ≤ 1+programBudget φ+CountedSupportRule.pairBudget n+
      CountedSubtypeSupport.queryBudget φ := by
  have hp := program_bound φ
  have hi := CountedSupportRule.pair_bound x y
  have hr := CountedSubtypeSupport.bound φ x y
  simp only [query, program_value, CountedSupportRule.pair_value]
  change 1+(program φ).2+(CountedSupportRule.pair x y).2+(CountedSubtypeSupport.query φ x y).2 ≤ _
  omega
end NSSE.ConstructedSupportQuery
