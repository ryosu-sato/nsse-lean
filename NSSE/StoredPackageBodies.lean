import NSSE.StoredFormulaRelabel

/-! Actual counted body construction for the existing existential packages.
Prefix-count construction and closing quantifiers are separate operations. -/
namespace NSSE.StoredPackageBodies
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage
variable {P : Type}

def leftName (m n : Nat) : P ⊕ Fin m → (P ⊕ Fin (m+n)) × Nat
  | .inl p => (.inl p,2)
  | .inr i => (.inr (Fin.castAdd n i),2)
def rightName (m n : Nat) : P ⊕ Fin n → (P ⊕ Fin (m+n)) × Nat
  | .inl p => (.inl p,2)
  | .inr i =>
    let a := CountedSupportRule.add m i.val
    (.inr ⟨a.1,by rw [CountedSupportRule.add_value]; omega⟩,2+a.2)

theorem left_value (m n : Nat) (x : P ⊕ Fin m) :
    (leftName m n x).1 = Sum.map id (Fin.castAdd n) x := by cases x <;> rfl
theorem right_value (m n : Nat) (x : P ⊕ Fin n) :
    (rightName m n x).1 = Sum.map id (Fin.natAdd m) x := by
  cases x with
  | inl p => rfl
  | inr i =>
    simp only [rightName,Sum.map_inr]
    congr 1
    apply Fin.ext
    exact CountedSupportRule.add_value m i.val
theorem left_bound (m n : Nat) (x : P ⊕ Fin m) : (leftName m n x).2 ≤ 2 := by
  cases x <;> rfl
theorem right_bound (m n : Nat) (x : P ⊕ Fin n) : (rightName m n x).2 ≤ m+3 := by
  cases x <;> simp only [rightName,CountedSupportRule.add_cost] <;> omega

def joinName (m n : Nat) : (P ⊕ Fin m) ⊕ Fin n → (P ⊕ Fin (m+n)) × Nat
  | .inl x => let a := leftName m n x; (a.1,1+a.2)
  | .inr i => let a := rightName m n (.inr i : P ⊕ Fin n); (a.1,1+a.2)
theorem join_value (m n : Nat) (x : (P ⊕ Fin m) ⊕ Fin n) :
    (joinName m n x).1 = Package.joinNames m n x := by
  cases x with
  | inl x => cases x <;> simp [joinName,left_value,Package.joinNames]
  | inr i => simp [joinName,right_value,Package.joinNames]
theorem join_bound (m n : Nat) (x : (P ⊕ Fin m) ⊕ Fin n) :
    (joinName m n x).2 ≤ m+4 := by
  cases x with
  | inl x => have h := left_bound m n x; simp only [joinName]; omega
  | inr i => have h := right_bound m n (.inr i : P ⊕ Fin n); simp only [joinName]; omega

def conjBody (A B : Package language P) : language.Formula (P ⊕ Fin (A.vars+B.vars)) × Nat :=
  let a := StoredFormulaRelabel.build (leftName A.vars B.vars) A.body
  let b := StoredFormulaRelabel.build (rightName A.vars B.vars) B.body
  (.imp (.imp a.1 (.imp b.1 .falsum)) .falsum,7+a.2+b.2)
def disjBody (A B : Package language P) : language.Formula (P ⊕ Fin (A.vars+B.vars)) × Nat :=
  let a := StoredFormulaRelabel.build (leftName A.vars B.vars) A.body
  let b := StoredFormulaRelabel.build (rightName A.vars B.vars) B.body
  (.imp (.imp a.1 .falsum) b.1,5+a.2+b.2)
def bindBody (m : Nat) (A : Package language (P ⊕ Fin m)) :
    language.Formula (P ⊕ Fin (m+A.vars)) × Nat :=
  StoredFormulaRelabel.build (joinName m A.vars) A.body

theorem conj_value (A B : Package language P) : (conjBody A B).1 = (A.conj B).body := by
  simp only [conjBody,StoredFormulaRelabel.formula_value,left_value,right_value,Package.conj]
  rfl
theorem disj_value (A B : Package language P) : (disjBody A B).1 = (A.disj B).body := by
  simp only [disjBody,StoredFormulaRelabel.formula_value,left_value,right_value,Package.disj]
  rfl
theorem bind_value (m : Nat) (A : Package language (P ⊕ Fin m)) :
    (bindBody m A).1 = (A.bind m).body := by
  simp only [bindBody,StoredFormulaRelabel.formula_value,join_value,Package.bind]

theorem conj_bound (A B : Package language P) :
    (conjBody A B).2 ≤ 7+9*nodes A.body+(11+2*A.vars)*nodes B.body := by
  have ha := StoredFormulaRelabel.bound (leftName A.vars B.vars) 2 (left_bound _ _) A.body
  have hb := StoredFormulaRelabel.bound (rightName A.vars B.vars) (A.vars+3) (right_bound _ _) B.body
  simp only [conjBody]; nlinarith
theorem disj_bound (A B : Package language P) :
    (disjBody A B).2 ≤ 5+9*nodes A.body+(11+2*A.vars)*nodes B.body := by
  have ha := StoredFormulaRelabel.bound (leftName A.vars B.vars) 2 (left_bound _ _) A.body
  have hb := StoredFormulaRelabel.bound (rightName A.vars B.vars) (A.vars+3) (right_bound _ _) B.body
  simp only [disjBody]; nlinarith
theorem bind_bound (m : Nat) (A : Package language (P ⊕ Fin m)) :
    (bindBody m A).2 ≤ (13+2*m)*nodes A.body := by
  have h := StoredFormulaRelabel.bound (joinName m A.vars) (m+4) (join_bound _ _) A.body
  simp only [bindBody]
  convert h using 1; ring
end NSSE.StoredPackageBodies
