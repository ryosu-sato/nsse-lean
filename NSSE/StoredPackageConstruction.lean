import NSSE.ConstructedPackageEvaluation

/-! Counted complete existential-package constructors. Equality transports
only align dependent witness indices; they erase and do not copy matrices.
The source-syntax and machine-cost boundary is unchanged from v1555. -/
namespace NSSE.StoredPackageConstruction
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage
variable {P : Type}

def assemble (n k : Nat) (h : n=k) (φ : language.Formula (P ⊕ Fin k)) (hf : φ.IsQF) :
    Package language P := ⟨n,h.symm ▸ φ,by cases h; exact hf⟩
theorem assemble_value (n k : Nat) (h : n=k) (φ : language.Formula (P ⊕ Fin k)) (hf : φ.IsQF) :
    assemble n k h φ hf = ⟨k,φ,hf⟩ := by cases h; rfl

def atom (φ : language.Formula P) (hf : φ.IsQF) : Package language P × Nat :=
  let a := StoredFormulaRelabel.build (fun p => ((Sum.inl p : P ⊕ Fin 0),1)) φ
  (⟨0,a.1,by rw [StoredFormulaRelabel.formula_value]; exact ExactReachabilityTable.relabel_qf φ hf _⟩,1+a.2)

def conj (A B : Package language P) : Package language P × Nat :=
  let s := CountedSupportRule.add A.vars B.vars
  let b := StoredPackageBodies.conjBody A B
  (assemble s.1 (A.vars+B.vars) (CountedSupportRule.add_value _ _) b.1
    (by rw [StoredPackageBodies.conj_value]; exact (A.conj B).qfree),1+s.2+b.2)
def disj (A B : Package language P) : Package language P × Nat :=
  let s := CountedSupportRule.add A.vars B.vars
  let b := StoredPackageBodies.disjBody A B
  (assemble s.1 (A.vars+B.vars) (CountedSupportRule.add_value _ _) b.1
    (by rw [StoredPackageBodies.disj_value]; exact (A.disj B).qfree),1+s.2+b.2)
def bind (m : Nat) (A : Package language (P ⊕ Fin m)) : Package language P × Nat :=
  let s := CountedSupportRule.add m A.vars
  let b := StoredPackageBodies.bindBody m A
  (assemble s.1 (m+A.vars) (CountedSupportRule.add_value _ _) b.1
    (by rw [StoredPackageBodies.bind_value]; exact (A.bind m).qfree),1+s.2+b.2)

theorem atom_value (φ : language.Formula P) (hf : φ.IsQF) :
    (atom φ hf).1 = Package.atom φ hf := by
  simp only [atom,StoredFormulaRelabel.formula_value,Package.atom]
theorem conj_value (A B : Package language P) : (conj A B).1 = A.conj B := by
  simp only [conj,assemble_value,StoredPackageBodies.conj_value]
  rfl
theorem disj_value (A B : Package language P) : (disj A B).1 = A.disj B := by
  simp only [disj,assemble_value,StoredPackageBodies.disj_value]
  rfl
theorem bind_value (m : Nat) (A : Package language (P ⊕ Fin m)) : (bind m A).1 = A.bind m := by
  simp only [bind,assemble_value,StoredPackageBodies.bind_value]
  rfl

theorem atom_bound (φ : language.Formula P) (hf : φ.IsQF) :
    (atom φ hf).2 ≤ 1+7*nodes φ := by
  have h := StoredFormulaRelabel.bound (fun p => ((Sum.inl p : P ⊕ Fin 0),1)) 1 (fun _ => le_rfl) φ
  simp only [atom]; omega
theorem conj_bound (A B : Package language P) :
    (conj A B).2 ≤ A.vars+9+9*nodes A.body+(11+2*A.vars)*nodes B.body := by
  have h := StoredPackageBodies.conj_bound A B
  simp only [conj,CountedSupportRule.add_cost]; omega
theorem disj_bound (A B : Package language P) :
    (disj A B).2 ≤ A.vars+7+9*nodes A.body+(11+2*A.vars)*nodes B.body := by
  have h := StoredPackageBodies.disj_bound A B
  simp only [disj,CountedSupportRule.add_cost]; omega
theorem bind_bound (m : Nat) (A : Package language (P ⊕ Fin m)) :
    (bind m A).2 ≤ m+2+(13+2*m)*nodes A.body := by
  have h := StoredPackageBodies.bind_bound m A
  simp only [bind,CountedSupportRule.add_cost]; omega
end NSSE.StoredPackageConstruction
