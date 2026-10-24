import NSSE.StoredPackageConstruction
import NSSE.ExistentialRowNonemptySize
import NSSE.StoredForwardTableBuild

/-! Counted finite package disjunction, matching the original nonemptiness
compiler's any operation. Callback construction costs are explicitly supplied. -/
namespace NSSE.StoredPackageDisjunction
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage
variable {P : Type}

def fold : List (Package language P) → Package language P × Nat
  | [] => StoredPackageConstruction.atom .falsum .falsum
  | A::as => let t := fold as; let r := StoredPackageConstruction.disj A t.1
    (r.1,1+t.2+r.2)
def original (as : List (Package language P)) :=
  as.foldr Package.disj (Package.atom ⊥ BoundedFormula.isQF_bot)
theorem value (as : List (Package language P)) : (fold as).1 = original as := by
  induction as with
  | nil => exact StoredPackageConstruction.atom_value _ _
  | cons A as ih => simp only [fold,StoredPackageConstruction.disj_value,ih,original,List.foldr_cons]

theorem original_nodes (as : List (Package language P)) (B : Nat)
    (hb : ∀ A ∈ as, nodes A.body ≤ B) : nodes (original as).body ≤ 1+as.length*(3+B) := by
  induction as with
  | nil => simp [original,Package.atom,nodes]
  | cons A as ih =>
    have ha := hb A (by simp)
    have ht := ih (fun A hA => hb A (by simp [hA]))
    simp only [original,List.foldr_cons,Package.disj,nodes_sup,nodes_relabel,List.length_cons] at *
    nlinarith
theorem original_vars (as : List (Package language P)) (V : Nat)
    (hv : ∀ A ∈ as, A.vars ≤ V) : (original as).vars ≤ as.length*V := by
  induction as with
  | nil => simp [original,Package.atom,nodes]
  | cons A as ih =>
    have ha := hv A (by simp)
    have ht := ih (fun A hA => hv A (by simp [hA]))
    simp only [original,List.foldr_cons,Package.disj,List.length_cons] at *
    nlinarith

def stepBudget (L V B : Nat) := V+8+9*B+(11+2*V)*(1+L*(3+B))
def budget (L V B : Nat) := 2+L*stepBudget L V B

theorem fold_bound (as : List (Package language P)) (L V B : Nat) (hl : as.length ≤ L)
    (hv : ∀ A ∈ as, A.vars ≤ V) (hb : ∀ A ∈ as, nodes A.body ≤ B) :
    (fold as).2 ≤ 2+as.length*stepBudget L V B := by
  induction as with
  | nil => simp [fold,StoredPackageConstruction.atom,StoredFormulaRelabel.build]
  | cons A as ih =>
    have hA := hv A (by simp); have hB := hb A (by simp)
    have ht := ih (by simp only [List.length_cons] at hl; omega)
      (fun A hA => hv A (by simp [hA])) (fun A hA => hb A (by simp [hA]))
    have hn := original_nodes as B (fun A hA => hb A (by simp [hA]))
    have hn' : nodes (fold as).1.body ≤ 1+L*(3+B) := by
      rw [value]
      apply hn.trans
      gcongr
      simp only [List.length_cons] at hl; omega
    have hs := StoredPackageConstruction.disj_bound A (fold as).1
    have hs' : (StoredPackageConstruction.disj A (fold as).1).2 ≤
        V+7+9*B+(11+2*V)*(1+L*(3+B)) := by
      apply hs.trans
      gcongr
    simp only [fold,List.length_cons,stepBudget] at *
    nlinarith

def any (n : Nat) (f : Fin n → Package language P × Nat) : Package language P × Nat :=
  let a := CountedFinEnumeration.tabulate n f
  let b := fold a.1
  (b.1,1+a.2+b.2)
theorem any_value (n : Nat) (f : Fin n → Package language P × Nat) :
    (any n f).1 = ExistentialRowNonempty.anyPackage n (fun i => (f i).1) := by
  simp only [any,value,original,CountedFinEnumeration.tabulate_value,ExistentialRowNonempty.anyPackage]
  rw [List.ofFn_eq_map]

theorem any_bound (n : Nat) (f : Fin n → Package language P × Nat) (c V B : Nat)
    (hc : ∀ i, (f i).2 ≤ c) (hv : ∀ i, (f i).1.vars ≤ V)
    (hb : ∀ i, nodes (f i).1.body ≤ B) :
    (any n f).2 ≤ 1+StoredForwardTableBuild.tabBudget n c+budget n V B := by
  have ha := CountedFinEnumeration.tabulate_bound n f c hc
  have hlen : (CountedFinEnumeration.tabulate n f).1.length = n := by
    simp only [CountedFinEnumeration.tabulate_value,List.length_ofFn]
  have ht := fold_bound (CountedFinEnumeration.tabulate n f).1 n V B (by omega)
    (by intro A hA; rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hA
        obtain ⟨i,rfl⟩ := hA; exact hv i)
    (by intro A hA; rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hA
        obtain ⟨i,rfl⟩ := hA; exact hb i)
  rw [hlen] at ht
  simp only [any,budget,StoredForwardTableBuild.tabBudget]
  omega
end NSSE.StoredPackageDisjunction
