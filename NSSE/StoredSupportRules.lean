import NSSE.StoredSubtypeInput
import NSSE.ConstructedSupportQuery

/-! Support rule generation from stored lists, including child lookup costs. -/
namespace NSSE.StoredSupportRules
open StoredSubtypeInput CountedListConstruction
variable {n d : Nat}

def decomp (a b : Bound n d) (i : Fin d) : HornRule × Nat :=
  let x := a.child i
  let y := b.child i
  let p := CountedSupportRule.pair x.1 y.1
  let h := CountedSupportRule.pair a.head b.head
  (⟨p.1,[h.1]⟩,5+x.2+y.2+p.2+h.2)

theorem decomp_value (a b : Bound n d) (i : Fin d) :
    (decomp a b i).1 = FiniteSubtypeSupport.decompRule a.denote b.denote i := by
  simp only [decomp, child_value, CountedSupportRule.pair_value, FiniteSubtypeSupport.decompRule, Bound.denote]

theorem decomp_bound (a b : Bound n d) (i : Fin d) :
    (decomp a b i).2 ≤ 5+2*d+2*CountedSupportRule.pairBudget n := by
  have hx := child_bound a i
  have hy := child_bound b i
  have hp := CountedSupportRule.pair_bound (a.child i).1 (b.child i).1
  have hh := CountedSupportRule.pair_bound a.head b.head
  simp only [decomp]; omega

def decompBudget (I : Input n d) :=
  productBudget I.lower.length I.upper.length d (5+2*d+2*CountedSupportRule.pairBudget n)

def rules (I : Input n d) : List HornRule × Nat :=
  let ns := CountedFinEnumeration.enumerate n
  let ds := CountedFinEnumeration.enumerate d
  let a := product3 CountedSupportRule.trans ns.1 ns.1 ns.1
  let b := product3 decomp I.lower I.upper ds.1
  let c := append a.1 b.1
  (c.1,2+ns.2+ds.2+a.2+b.2+c.2)

theorem value (I : Input n d) : (rules I).1 = (FiniteSubtypeSupport.compiler I.denote).rules := by
  simp only [rules, CountedFinEnumeration.value, append_value, product3_value,
    CountedSupportRule.trans_value, decomp_value, FiniteSubtypeSupport.compiler,
    FiniteSubtypeSupport.transRules, FiniteSubtypeSupport.decompRules, Input.denote,
    List.flatMap_map, Function.comp_def]

def budget (I : Input n d) :=
  4+(n+1)^2+(d+1)^2+CountedSupportRules.transBudget n+decompBudget I+n*n*n

theorem bound (I : Input n d) : (rules I).2 ≤ budget I := by
  have hn := CountedFinEnumeration.bound n
  have hd := CountedFinEnumeration.bound d
  have ht := CountedSupportRules.trans_bound n
  have he := product3_bound decomp I.lower I.upper (List.finRange d) _ decomp_bound
  simp only [List.length_finRange] at he
  simp only [rules, CountedFinEnumeration.value, append_cost]
  change 2+_+_+(CountedSupportRules.trans n).2+_+((CountedSupportRules.trans n).1.length+1) ≤ _
  rw [CountedSupportRules.trans_value, CountedSubtypeSupport.trans_length]
  dsimp only [budget, decompBudget]
  omega
end NSSE.StoredSupportRules
