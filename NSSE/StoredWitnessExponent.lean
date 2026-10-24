import NSSE.CountedNaturalPower

/-! Counted original witness exponent from actual stored row dimensions. -/
namespace NSSE.StoredWitnessExponent
variable {R : Nat → Type} {P : Type} {k : Nat} {ns : Fin k → Nat}

def row (n : Nat) : Nat × Nat :=
  let a := CountedNaturalPower.build n 6
  let b := CountedNaturalPower.build n 8
  let x := CountedSupportRule.mul 2 a.1
  let y := CountedSupportRule.mul 8 b.1
  let z := CountedSupportRule.add x.1 y.1
  (z.1,5+a.2+b.2+x.2+y.2+z.2)
theorem row_value (n : Nat) : (row n).1 = UnifiedBlockWitnessBound.rowExponent n := by
  simp only [row,CountedNaturalPower.value,CountedSupportRule.mul_value,CountedSupportRule.add_value,
    UnifiedBlockWitnessBound.rowExponent]
def rowBudget (n : Nat) := 8+CountedNaturalPower.budget n 6+CountedNaturalPower.budget n 8+6*n^6+10*n^8
theorem row_bound (n : Nat) : (row n).2 ≤ rowBudget n := by
  have h6 := CountedNaturalPower.bound n 6
  have h8 := CountedNaturalPower.bound n 8
  simp only [row,rowBudget,CountedNaturalPower.value,CountedSupportRule.mul_cost,CountedSupportRule.add_cost,
    CountedSupportRule.mul_value]
  omega
theorem rowBudget_mono {a b : Nat} (h : a ≤ b) : rowBudget a ≤ rowBudget b := by
  unfold rowBudget CountedNaturalPower.budget
  gcongr

def sum : List Nat → Nat × Nat
  | [] => (0,1)
  | x::xs => let a := sum xs; let b := CountedSupportRule.add x a.1; (b.1,2+a.2+b.2)
theorem sum_value (xs : List Nat) : (sum xs).1 = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sum,CountedSupportRule.add_value,ih,List.sum_cons]
theorem sum_cost (xs : List Nat) : (sum xs).2 = 1+3*xs.length+xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sum,CountedSupportRule.add_cost,ih,List.length_cons,List.sum_cons]; omega

def entries (A : StoredRelationArrayPackage.Family R P ns) : List Nat × Nat :=
  CountedFinEnumeration.tabulate k fun i =>
    let a := StoredRelationTuple.read A.entries i
    let b := row a.1.1
    (b.1,1+a.2+b.2)
theorem entries_value (A : StoredRelationArrayPackage.Family R P ns) :
    (entries A).1 = List.ofFn (fun i => UnifiedBlockWitnessBound.rowExponent (ns i)) := by
  simp only [entries,CountedFinEnumeration.tabulate_value,row_value,A.dimensions]
theorem entries_bound (A : StoredRelationArrayPackage.Family R P ns) (N : Nat) (hn : ∀ i, ns i ≤ N) :
    (entries A).2 ≤ StoredForwardTableBuild.tabBudget k (1+k+rowBudget N) := by
  apply CountedFinEnumeration.tabulate_bound
  intro i
  have ha := StoredRelationTuple.read_bound A.entries i
  have hb := row_bound (StoredRelationTuple.read A.entries i).1.1
  rw [A.dimensions i] at hb
  have hm := rowBudget_mono (hn i)
  dsimp only
  rw [A.dimensions i]
  omega

def build (A : StoredRelationArrayPackage.Family R P ns) (c : Nat) : Nat × Nat :=
  let a := row c
  let b := entries A
  let s := sum b.1
  let d := CountedSupportRule.add a.1 s.1
  let e := CountedSupportRule.add 1 d.1
  (e.1,5+a.2+b.2+s.2+d.2+e.2)
theorem value (A : StoredRelationArrayPackage.Family R P ns) (c : Nat) :
    (build A c).1 = UnifiedBlockWitnessBound.exponent ns c := by
  simp only [build,CountedSupportRule.add_value,row_value,sum_value,entries_value,List.sum_ofFn,
    UnifiedBlockWitnessBound.exponent]
  omega

def budget (k N : Nat) := 9+rowBudget N+StoredForwardTableBuild.tabBudget k (1+k+rowBudget N)+3*k+
  (k+1)*UnifiedBlockWitnessBound.rowExponent N
theorem bound (A : StoredRelationArrayPackage.Family R P ns) (c N : Nat) (hc : c ≤ N) (hn : ∀ i, ns i ≤ N) :
    (build A c).2 ≤ budget k N := by
  have ha := (row_bound c).trans (rowBudget_mono hc)
  have hb := entries_bound A N hn
  have hs := sum_cost (entries A).1
  have hv : (entries A).1.sum ≤ k*UnifiedBlockWitnessBound.rowExponent N := by
    rw [entries_value,List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin k, UnifiedBlockWitnessBound.rowExponent N := Finset.sum_le_sum (fun i _ => UnifiedBlockWitnessBound.rowExponent_mono (hn i))
      _ = _ := by simp
  have hl : (entries A).1.length = k := by rw [entries_value,List.length_ofFn]
  have hr := UnifiedBlockWitnessBound.rowExponent_mono hc
  rw [hl] at hs
  simp only [build,budget,CountedSupportRule.add_cost,row_value]
  nlinarith
end NSSE.StoredWitnessExponent
