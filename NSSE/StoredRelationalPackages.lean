import NSSE.StoredRelationalClosure

/-! Stored Package composition for arbitrary finite relation arities.
All tuple renaming traverses stored lists. Equality transports erase. -/
namespace NSSE.StoredRelationalPackages
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure
open StoredPackageBodies
variable {R : Nat → Type} {P : Type}

def conjBody (A B : Package R P) : Data R (P ⊕ Fin (A.vars+B.vars)) 0 × Nat :=
  let a := rename (leftName A.vars B.vars) A.body
  let b := rename (rightName A.vars B.vars) B.body
  (.imp (.imp a.1 (.imp b.1 .falsum)) .falsum,7+a.2+b.2)
def disjBody (A B : Package R P) : Data R (P ⊕ Fin (A.vars+B.vars)) 0 × Nat :=
  let a := rename (leftName A.vars B.vars) A.body
  let b := rename (rightName A.vars B.vars) B.body
  (.imp (.imp a.1 .falsum) b.1,5+a.2+b.2)
def bindBody (m : Nat) (A : Package R (P ⊕ Fin m)) :
    Data R (P ⊕ Fin (m+A.vars)) 0 × Nat :=
  rename (joinName m A.vars) A.body

theorem conj_value (A B : Package R P) : denote (conjBody A B).1 = (A.original.conj B.original).body := by
  simp only [conjBody,denote,Package.original,formula_value,left_value,right_value,ExistentialFormulaPackage.Package.conj]
  rfl
theorem disj_value (A B : Package R P) : denote (disjBody A B).1 = (A.original.disj B.original).body := by
  simp only [disjBody,denote,Package.original,formula_value,left_value,right_value,ExistentialFormulaPackage.Package.disj]
  rfl
theorem bind_value (m : Nat) (A : Package R (P ⊕ Fin m)) :
    denote (bindBody m A).1 = (A.original.bind m).body := by
  simp only [bindBody,Package.original,formula_value,join_value,ExistentialFormulaPackage.Package.bind]


def assemble (n k : Nat) (h : n=k) (φ : Data R (P ⊕ Fin k) 0) (hf : (denote φ).IsQF) :
    Package R P := ⟨n,h.symm ▸ φ,by cases h; exact hf⟩
theorem assemble_value (n k : Nat) (h : n=k) (φ : Data R (P ⊕ Fin k) 0) (hf : (denote φ).IsQF) :
    assemble n k h φ hf = ⟨k,φ,hf⟩ := by cases h; rfl

def atom (φ : Data R P 0) (hf : (denote φ).IsQF) : Package R P × Nat :=
  let a := rename (fun p => ((Sum.inl p : P ⊕ Fin 0),1)) φ
  (⟨0,a.1,by rw [formula_value]; exact ExactReachabilityTable.relabel_qf _ hf _⟩,1+a.2)
def conj (A B : Package R P) : Package R P × Nat :=
  let s := CountedSupportRule.add A.vars B.vars
  let b := conjBody A B
  (assemble s.1 (A.vars+B.vars) (CountedSupportRule.add_value _ _) b.1
    (by rw [conj_value]; exact (A.original.conj B.original).qfree),1+s.2+b.2)
def disj (A B : Package R P) : Package R P × Nat :=
  let s := CountedSupportRule.add A.vars B.vars
  let b := disjBody A B
  (assemble s.1 (A.vars+B.vars) (CountedSupportRule.add_value _ _) b.1
    (by rw [disj_value]; exact (A.original.disj B.original).qfree),1+s.2+b.2)
def bind (m : Nat) (A : Package R (P ⊕ Fin m)) : Package R P × Nat :=
  let s := CountedSupportRule.add m A.vars
  let b := bindBody m A
  (assemble s.1 (m+A.vars) (CountedSupportRule.add_value _ _) b.1
    (by rw [bind_value]; exact (A.original.bind m).qfree),1+s.2+b.2)

theorem atom_original (φ : Data R P 0) (hf : (denote φ).IsQF) :
    (atom φ hf).1.original = ExistentialFormulaPackage.Package.atom (denote φ) hf := by
  simp only [atom,Package.original,formula_value,ExistentialFormulaPackage.Package.atom]
theorem conj_original (A B : Package R P) :
    (conj A B).1.original = A.original.conj B.original := by
  dsimp only [conj]
  rw [assemble_value]
  simp only [Package.original,conj_value]
  rfl
theorem disj_original (A B : Package R P) :
    (disj A B).1.original = A.original.disj B.original := by
  dsimp only [disj]
  rw [assemble_value]
  simp only [Package.original,disj_value]
  rfl
theorem bind_original (m : Nat) (A : Package R (P ⊕ Fin m)) :
    (bind m A).1.original = A.original.bind m := by
  dsimp only [bind]
  rw [assemble_value]
  simp only [Package.original,bind_value]
  rfl

theorem atom_bound (φ : Data R P 0) (hf : (denote φ).IsQF) (K : Nat) (hk : arity φ ≤ K) :
    (atom φ hf).2 ≤ 1+weight K 1*nodes φ := by
  have h := rename_bound (fun p => ((Sum.inl p : P ⊕ Fin 0),1)) 1 K (fun _ => le_rfl) φ hk
  simp only [atom]; omega
theorem conj_bound (A B : Package R P) (K : Nat) (ha : arity A.body ≤ K) (hb : arity B.body ≤ K) :
    (conj A B).2 ≤ A.vars+9+weight K 2*nodes A.body+weight K (A.vars+3)*nodes B.body := by
  have h₁ := rename_bound (leftName A.vars B.vars) 2 K (left_bound _ _) A.body ha
  have h₂ := rename_bound (rightName A.vars B.vars) (A.vars+3) K (right_bound _ _) B.body hb
  simp only [conj,conjBody,CountedSupportRule.add_cost]; omega
theorem disj_bound (A B : Package R P) (K : Nat) (ha : arity A.body ≤ K) (hb : arity B.body ≤ K) :
    (disj A B).2 ≤ A.vars+7+weight K 2*nodes A.body+weight K (A.vars+3)*nodes B.body := by
  have h₁ := rename_bound (leftName A.vars B.vars) 2 K (left_bound _ _) A.body ha
  have h₂ := rename_bound (rightName A.vars B.vars) (A.vars+3) K (right_bound _ _) B.body hb
  simp only [disj,disjBody,CountedSupportRule.add_cost]; omega
theorem bind_bound (m : Nat) (A : Package R (P ⊕ Fin m)) (K : Nat) (hk : arity A.body ≤ K) :
    (bind m A).2 ≤ m+2+weight K (m+4)*nodes A.body := by
  have h := rename_bound (joinName m A.vars) (m+4) K (join_bound _ _) A.body hk
  simp only [bind,bindBody,CountedSupportRule.add_cost]; omega
theorem atom_shape (φ : Data R P 0) (hf : (denote φ).IsQF) :
    (atom φ hf).1.vars = 0 ∧ nodes (atom φ hf).1.body = nodes φ ∧
    arity (atom φ hf).1.body = arity φ := by
  simp only [atom,rename_nodes,rename_arity,and_self]
theorem conj_shape (A B : Package R P) :
    (conj A B).1.vars = A.vars+B.vars ∧
    nodes (conj A B).1.body = 5+nodes A.body+nodes B.body ∧
    arity (conj A B).1.body = max (arity A.body) (arity B.body) := by
  dsimp only [conj]
  rw [assemble_value]
  simp [conjBody,nodes,arity,rename_nodes,rename_arity,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  omega
theorem disj_shape (A B : Package R P) :
    (disj A B).1.vars = A.vars+B.vars ∧
    nodes (disj A B).1.body = 3+nodes A.body+nodes B.body ∧
    arity (disj A B).1.body = max (arity A.body) (arity B.body) := by
  dsimp only [disj]
  rw [assemble_value]
  simp [disjBody,nodes,arity,rename_nodes,rename_arity,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  omega
theorem bind_shape (m : Nat) (A : Package R (P ⊕ Fin m)) :
    (bind m A).1.vars = m+A.vars ∧ nodes (bind m A).1.body = nodes A.body ∧
    arity (bind m A).1.body = arity A.body := by
  dsimp only [bind]
  rw [assemble_value]
  simp only [bindBody,rename_nodes,rename_arity,and_self]
end NSSE.StoredRelationalPackages
