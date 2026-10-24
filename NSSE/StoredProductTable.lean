import NSSE.StoredCapPreparation
import Mathlib.Data.List.OfFn

namespace NSSE.StoredProductTable
open CountedFinEnumeration StoredForwardTableBuild

def build {α : Type*} (n m : Nat) (f : Fin n → Fin m → α × Nat) : List α × Nat :=
  let xs := CountedFinEnumeration.enumerate n
  let r := CountedListConstruction.flatMap (fun q => tabulate m (f q)) xs.1
  (r.1,1+xs.2+r.2)

theorem value {α : Type*} (n m : Nat) (f : Fin n → Fin m → α × Nat) :
    (build n m f).1 = List.ofFn (fun q : Fin (n*m) =>
      (f (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).1) := by
  simp only [build,CountedListConstruction.flatMap_value,CountedFinEnumeration.value,
    CountedFinEnumeration.tabulate_value]
  rw [List.ofFn_mul]
  simp only [List.flatMap, ← List.ofFn_eq_map]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val*m+j.val,by have hi := Nat.mul_le_mul_right m i.isLt; have hj := j.isLt; nlinarith⟩ : Fin (n*m)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [h,Equiv.symm_apply_apply]

def budget (n m c : Nat) := 2+(n+1)^2+n*(2+tabBudget m c+m)

theorem bound {α : Type*} (n m c : Nat) (f : Fin n → Fin m → α × Nat)
    (h : ∀ q r, (f q r).2 ≤ c) : (build n m f).2 ≤ budget n m c := by
  have he := CountedFinEnumeration.bound n
  have hr := CountedListConstruction.flatMap_bound (fun q => tabulate m (f q))
    (CountedFinEnumeration.enumerate n).1 (tabBudget m c) m
    (fun q _ => tabulate_bound m (f q) c (h q))
    (fun q _ => by simp only [tabulate_value,List.length_ofFn]; rfl)
  simp only [CountedFinEnumeration.value,List.length_finRange] at hr
  simp only [build,budget,CountedFinEnumeration.value]
  omega
end NSSE.StoredProductTable
