import NSSE.StoredDFAProductBuild

namespace NSSE.StoredDFAUnions
variable {d : Nat}

def constant (d : Nat) (b : Bool) : StoredOrdinaryDFABuild.Data × Nat :=
  let t := StoredOrdinaryDFABuild.rows 1 d (fun q _ => (q.val,1))
  (⟨1,0,t.1,[b]⟩,4+t.2)

def constantBudget (d : Nat) := 4+StoredForwardTableBuild.tabBudget 1 (StoredForwardTableBuild.tabBudget d 1)

theorem constant_bound (d : Nat) (b : Bool) : (constant d b).2 ≤ constantBudget d := by
  have h := StoredOrdinaryDFABuild.rows_bound 1 d 1 (fun q _ => (q.val,1)) (fun _ _ => le_rfl)
  exact Nat.add_le_add_left h 4

theorem constant_value (d : Nat) (b : Bool) : (constant d b).1 =
    StoredOrdinaryDFABuild.snapshot (FiniteDFAOperations.constant (α := Fin d) b) := by
  simp only [constant,StoredOrdinaryDFABuild.rows_value,StoredOrdinaryDFABuild.snapshot,
    FiniteDFAOperations.constant,Bool.decide_coe]
  rfl

def build : List StoredOrdinaryDFABuild.Data → StoredOrdinaryDFABuild.Data × Nat
  | [] => constant d false
  | a::as =>
    let r := build as
    let p := StoredDFAProductBuild.build (d := d) a r.1 (· || ·)
    (p.1,1+r.2+p.2)

def budget (d : Nat) : List Nat → Nat
  | [] => constantBudget d
  | n::ns => 1+budget d ns+StoredDFAProductBuild.budget n ns.prod d

theorem count (as : List StoredOrdinaryDFABuild.Data) :
    (build (d := d) as).1.count = (as.map StoredOrdinaryDFABuild.Data.count).prod := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [build,StoredDFAProductBuild.count,ih,List.map_cons,List.prod_cons]

theorem value (as : List (FiniteSOARankDecision.InputDFA (Fin d))) :
    (build (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteDFAOperations.unions as) := by
  induction as with
  | nil => exact constant_value d false
  | cons a as ih =>
    simp only [List.map_cons,build,ih,StoredDFAProductBuild.union_value,FiniteDFAOperations.unions]

theorem bound (as : List (FiniteSOARankDecision.InputDFA (Fin d))) :
    (build (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).2 ≤
      budget d (as.map FiniteSOARankDecision.InputDFA.count) := by
  induction as with
  | nil => exact constant_bound d false
  | cons a as ih =>
    have hp := StoredDFAProductBuild.bound (d := d) (StoredOrdinaryDFABuild.snapshot a)
      (build (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).1 (· || ·)
      (StoredDFAProductCells.valid_snapshot a)
      (by rw [value]; exact StoredDFAProductCells.valid_snapshot _)
    have hc := count (d := d) (as.map StoredOrdinaryDFABuild.snapshot)
    simp only [List.map_map,StoredOrdinaryDFABuild.snapshot] at hc
    rw [hc] at hp
    simp only [List.map_cons,build,budget]
    change 1+(build (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).2+_ ≤ _
    change (StoredDFAProductBuild.build (d := d) (StoredOrdinaryDFABuild.snapshot a)
      (build (d := d) (as.map StoredOrdinaryDFABuild.snapshot)).1 (· || ·)).2 ≤
      StoredDFAProductBuild.budget a.count (as.map FiniteSOARankDecision.InputDFA.count).prod d at hp
    omega
end NSSE.StoredDFAUnions
