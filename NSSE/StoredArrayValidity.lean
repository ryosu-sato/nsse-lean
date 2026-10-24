import NSSE.StoredArrayEquality

/-! Stored prefix-validity formulas with counted coordinate construction. -/
namespace NSSE.StoredArrayValidity
open FirstOrder FirstOrder.Language StoredRelationalFormula FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {q T : Nat}

def every (m : Nat) (f : Fin m → Data R P 0 × Nat) : Data R P 0 × Nat :=
  let a := CountedFinEnumeration.tabulate m f
  let b := StoredArrayEquality.fold a.1
  (b.1,1+a.2+b.2)
theorem every_value (m : Nat) (f : Fin m → Data R P 0 × Nat) :
    denote (every m f).1 = ExactReachabilityTable.every m (fun i => denote (f i).1) := by
  simp only [every,StoredArrayEquality.fold_value,CountedFinEnumeration.tabulate_value,List.map_ofFn,
    ExactReachabilityTable.every]
  rw [List.ofFn_eq_map]
  rfl
def everyBudget (m c : Nat) := 4+StoredForwardTableBuild.tabBudget m c+6*m
theorem every_bound (m : Nat) (f : Fin m → Data R P 0 × Nat) (c : Nat) (hc : ∀ i, (f i).2 ≤ c) :
    (every m f).2 ≤ everyBudget m c := by
  have h := CountedFinEnumeration.tabulate_bound m f c hc
  simp only [every,StoredArrayEquality.fold_cost,CountedFinEnumeration.tabulate_value,List.length_ofFn,
    everyBudget,StoredForwardTableBuild.tabBudget] at *
  omega

def step (one : P) (t : Fin T) (i : Fin q) : Data R (Params P q T) 0 × Nat :=
  let a := StoredArrayCoordinates.flag (P := P) t.succ i
  let b := StoredArrayCoordinates.flag (P := P) t.castSucc i
  (.imp (.equal (.inl a.1) (.inl (.inl one))) (.equal (.inl b.1) (.inl (.inl one))),8+a.2+b.2)
theorem step_value (zero one : P) (t : Fin T) (i : Fin q) :
    denote (step (R := R) one t i).1 =
      (DynamicColumnSelection.flag (.inl one) (flags zero q T (t.val+1) i)).imp
        (DynamicColumnSelection.flag (.inl one) (flags zero q T t.val i)) := by
  simp only [step,denote,StoredArrayCoordinates.flag_value zero,Fin.val_succ,Fin.coe_castSucc,
    DynamicColumnSelection.flag]
  rfl
def stepBudget (q T : Nat) := 8+2*StoredArrayCoordinates.flagBudget q T
theorem step_bound (one : P) (t : Fin T) (i : Fin q) :
    (step (R := R) one t i).2 ≤ stepBudget q T := by
  have ha := StoredArrayCoordinates.flag_bound (P := P) t.succ i
  have hb := StoredArrayCoordinates.flag_bound (P := P) t.castSucc i
  simp only [step,stepBudget]; omega

def build (one : P) (q T : Nat) : Data R (Params P q T) 0 × Nat :=
  every T (fun t => every q (fun i => step one t i))
theorem value (zero one : P) : denote (build (R := R) one q T).1 = FiniteWordArrayRepresentation.valid zero one q T := by
  simp only [build,every_value,step_value zero,FiniteWordArrayRepresentation.valid,PrefixArrayValidity.formula]
def budget (q T : Nat) := everyBudget T (everyBudget q (stepBudget q T))
theorem bound (one : P) : (build (R := R) one q T).2 ≤ budget q T :=
  every_bound T _ _ (fun t => every_bound q _ _ (fun i => step_bound one t i))
theorem qfree (zero one : P) : (denote (build (R := R) one q T).1).IsQF := by
  rw [value zero]
  exact PrefixArrayValidity.formula_qf _ _ _
theorem nodes_value (zero one : P) : nodes (build (R := R) one q T).1 = 3+T*(8+8*q) := by
  rw [← denote_nodes,value zero]
  exact PrefixArrayValidity.nodes_formula _ _ _
theorem every_arity (m : Nat) (f : Fin m → Data R P 0 × Nat) (hf : ∀ i, arity (f i).1 = 0) :
    arity (every m f).1 = 0 := by
  apply StoredArrayEquality.fold_arity
  intro φ hφ
  rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hφ
  obtain ⟨i,rfl⟩ := hφ
  exact hf i
theorem arity_value (one : P) : arity (build (R := R) one q T).1 = 0 :=
  every_arity T _ (fun _ => every_arity q _ (fun _ => rfl))
def package (zero one : P) (q T : Nat) : StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := build one q T
  let b := StoredRelationalPackages.atom a.1 (qfree zero one)
  (b.1,1+a.2+b.2)
theorem package_value (zero one : P) :
    (package (R := R) zero one q T).1.original = ExistentialFormulaPackage.Package.atom
      (FiniteWordArrayRepresentation.valid zero one q T) (PrefixArrayValidity.formula_qf _ _ _) := by
  simp only [package,StoredRelationalPackages.atom_original,value zero]
theorem package_bound (zero one : P) :
    (package (R := R) zero one q T).2 ≤ 2+budget q T+5*(3+T*(8+8*q)) := by
  have hb := bound (R := R) (q := q) (T := T) one
  have hn := nodes_value (R := R) (q := q) (T := T) zero one
  have ha := StoredRelationalPackages.atom_bound (build (R := R) one q T).1 (qfree zero one) 0
    (by rw [arity_value])
  simp only [weight] at ha
  simp only [package]; omega
end NSSE.StoredArrayValidity
