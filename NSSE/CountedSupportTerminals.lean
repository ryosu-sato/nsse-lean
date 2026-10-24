import NSSE.CountedFinEnumeration
import NSSE.CountedRegularSatisfiability

/-! Support terminal tables constructed by counted diagonal tests.
No uncounted quotient/remainder calculation is used in this constructor. -/
namespace NSSE.CountedSupportTerminals
open FiniteSubtypeSupport CountedRegularSatisfiability FiniteValuationLookup
variable {n : Nat}

def diagonal (s : Fin (n*n)) (x : Fin n) : Bool × Nat :=
  let p := CountedSupportRule.pair x x
  let e := equalNat s.val p.1
  (e.1,1+p.2+e.2)

theorem diagonal_correct (s : Fin (n*n)) (x : Fin n) :
    (diagonal s x).1 = true ↔ s.val = pairId x x := by
  simp only [diagonal, equalNat_correct, CountedSupportRule.pair_value]

theorem diagonal_bound (s : Fin (n*n)) (x : Fin n) :
    (diagonal s x).2 ≤ 1+CountedSupportRule.pairBudget n+n*n := by
  have hp := CountedSupportRule.pair_bound x x
  have he := equalNat_bound s.val (CountedSupportRule.pair x x).1
  have hs := s.isLt
  simp only [diagonal]; omega

def cell (s : Fin (n*n)) : Bool × Nat :=
  let r := CountedFinEnumeration.enumerate n
  let b := any (r.1.map (diagonal s))
  (b.1,1+r.2+b.2)

theorem cell_correct (s : Fin (n*n)) :
    (cell s).1 = true ↔ ∃ x : Fin n, s.val = pairId x x := by
  simp [cell, any, CountedFinEnumeration.value, List.any_map, Function.comp_def, diagonal_correct]

theorem cell_value (s : Fin (n*n)) : (cell s).1 = terminal n s.val := by
  apply Bool.eq_iff_iff.mpr
  rw [cell_correct]
  constructor
  · rintro ⟨x,hx⟩
    rw [hx]
    exact (terminal_pair x x).mpr rfl
  · intro ht
    let p : Fin n × Fin n := finProdFinEquiv.symm s
    have he : pairId p.1 p.2 = s.val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply s)
    have hp : p.1=p.2 := (terminal_pair p.1 p.2).mp (by rwa [he])
    refine ⟨p.1,?_⟩
    rw [hp]
    simpa only [hp] using he.symm

def cellBudget (n : Nat) := 2+(n+1)^2+n*(2+CountedSupportRule.pairBudget n+n*n)

theorem cell_bound (s : Fin (n*n)) : (cell s).2 ≤ cellBudget n := by
  have hr := CountedFinEnumeration.bound n
  have hb := any_bound (List.finRange n) (diagonal s)
    (1+CountedSupportRule.pairBudget n+n*n) (fun x _ => diagonal_bound s x)
  simp only [List.length_finRange, ← Nat.add_assoc] at hb
  norm_num only [Nat.reduceAdd] at hb
  simp only [cell, CountedFinEnumeration.value, cellBudget]
  omega

def table (n : Nat) : List Bool × Nat := CountedFinEnumeration.tabulate (n*n) cell

theorem table_value (n : Nat) :
    (table n).1 = ExplicitUnaryTableLanguage.tabulate (fun s : Fin (n*n) => terminal n s.val) := by
  simp only [table, CountedFinEnumeration.tabulate_value, cell_value, ExplicitUnaryTableLanguage.tabulate]

theorem table_bound (n : Nat) :
    (table n).2 ≤ 2+(n*n+1)^2+n*n*(1+cellBudget n) :=
  CountedFinEnumeration.tabulate_bound (n*n) cell (cellBudget n) cell_bound
end NSSE.CountedSupportTerminals
