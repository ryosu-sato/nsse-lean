import NSSE.CountedListConstruction

/-! Actual support rule lists with counted arithmetic and list construction.
finRange generation and input child lookup are still separate costs. -/
namespace NSSE.CountedSupportRules
open SubtypeConstraints CountedListConstruction
variable {n d : Nat}

def trans (n : Nat) : List HornRule × Nat :=
  product3 CountedSupportRule.trans (List.finRange n) (List.finRange n) (List.finRange n)
def decomp (φ : Constraints n d) : List HornRule × Nat :=
  product3 CountedSupportRule.decomp φ.lower φ.upper (List.finRange d)

theorem trans_value (n : Nat) : (trans n).1 = FiniteSubtypeSupport.transRules n := by
  simp only [trans, product3_value, CountedSupportRule.trans_value, FiniteSubtypeSupport.transRules]
theorem decomp_value (φ : Constraints n d) : (decomp φ).1 = FiniteSubtypeSupport.decompRules φ := by
  simp only [decomp, product3_value, CountedSupportRule.decomp_value, FiniteSubtypeSupport.decompRules]

def transBudget (n : Nat) := productBudget n n n (4+3*CountedSupportRule.pairBudget n)
def decompBudget (φ : Constraints n d) :=
  productBudget φ.lower.length φ.upper.length d (3+2*CountedSupportRule.pairBudget n)

theorem trans_bound (n : Nat) : (trans n).2 ≤ transBudget n := by
  simpa only [List.length_finRange] using product3_bound CountedSupportRule.trans
    (List.finRange n) (List.finRange n) (List.finRange n) _ CountedSupportRule.trans_bound
theorem decomp_bound (φ : Constraints n d) : (decomp φ).2 ≤ decompBudget φ := by
  simpa only [List.length_finRange] using product3_bound CountedSupportRule.decomp
    φ.lower φ.upper (List.finRange d) _ CountedSupportRule.decomp_bound

def rules (φ : Constraints n d) : List HornRule × Nat :=
  let a := trans n
  let b := decomp φ
  let c := append a.1 b.1
  (c.1,1+a.2+b.2+c.2)

theorem value (φ : Constraints n d) : (rules φ).1 = (FiniteSubtypeSupport.compiler φ).rules := by
  simp only [rules, append_value, trans_value, decomp_value, FiniteSubtypeSupport.compiler]

theorem bound (φ : Constraints n d) :
    (rules φ).2 ≤ 2+transBudget n+decompBudget φ+n*n*n := by
  have ht := trans_bound n
  have hd := decomp_bound φ
  simp only [rules, append_cost, trans_value, CountedSubtypeSupport.trans_length]
  omega
end NSSE.CountedSupportRules
