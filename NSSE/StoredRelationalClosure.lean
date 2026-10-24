import NSSE.StoredRelationalFormula

/-! Counted existential closure of stored, arbitrary-arity matrices.
The semantic renderer is used only in theorem statements and proofs. -/
namespace NSSE.StoredRelationalClosure
open FirstOrder FirstOrder.Language StoredRelationalFormula
variable {R : Nat → Type} {P : Type} {k : Nat}

def strip : (P ⊕ Fin k) ⊕ Fin 0 → (P ⊕ Fin k) × Nat
  | .inl x => (x,2)
  | .inr i => Fin.elim0 i

theorem strip_cost (x : (P ⊕ Fin k) ⊕ Fin 0) : (strip x).2 = 2 := by
  cases x with
  | inl x => rfl
  | inr i => exact Fin.elim0 i

theorem strip_value (x : (P ⊕ Fin k) ⊕ Fin 0) :
    (strip x).1 = BoundedFormula.relabelAux (fun x : P ⊕ Fin k => x) 0 x := by
  cases x with
  | inl x => cases x <;> rfl
  | inr i => exact Fin.elim0 i

def matrix : (φ : Data R (P ⊕ Fin k) 0) → (denote φ).IsQF → Data R P k × Nat
  | .falsum, _ => (.falsum,1)
  | .equal x y, _ => let a := strip x; let b := strip y
    (.equal a.1 b.1,1+a.2+b.2)
  | .rel r args, _ => let a := StoredRelationTuple.map strip args
    (.rel r a.1,1+a.2)
  | .imp φ ψ, h =>
    let a := matrix φ (by cases h with | imp hφ _ => exact hφ | of_isAtomic ha => cases ha)
    let b := matrix ψ (by cases h with | imp _ hψ => exact hψ | of_isAtomic ha => cases ha)
    (.imp a.1 b.1,1+a.2+b.2)
  | .all φ, h => False.elim (BoundedFormula.not_all_isQF (denote φ) h)

theorem matrix_value (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF) :
    denote (matrix φ h).1 = BoundedFormula.relabel (fun x => x) (denote φ) := by
  cases φ with
  | falsum => simp [matrix,denote,BoundedFormula.relabel,BoundedFormula.mapTermRel]
  | equal x y =>
    simp only [matrix,denote,BoundedFormula.relabel,BoundedFormula.mapTermRel,Term.relabel,strip_value]
  | rel r args =>
    simp only [matrix,denote,BoundedFormula.relabel,BoundedFormula.mapTermRel]
    congr 1
    funext i
    simp only [StoredRelationTuple.map_read,strip_value,Term.relabel]
  | imp φ ψ =>
    simp only [matrix,denote,BoundedFormula.relabel_imp]
    rw [matrix_value φ, matrix_value ψ]
  | all φ => exact False.elim (BoundedFormula.not_all_isQF (denote φ) h)

theorem matrix_bound (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF)
    (K : Nat) (hk : arity φ ≤ K) : (matrix φ h).2 ≤ (5+3*K)*nodes φ := by
  cases φ with
  | falsum => simp only [matrix,nodes]; omega
  | equal x y => simp only [matrix,nodes,strip_cost,Nat.mul_one]; omega
  | @rel n a r args =>
    have hb := StoredRelationTuple.map_bound strip args 2 (fun x => le_of_eq (strip_cost x))
    simp only [arity] at hk
    simp only [matrix,nodes,Nat.mul_one]
    omega
  | imp φ ψ =>
    simp only [arity,max_le_iff] at hk
    have hl : (denote φ).IsQF := by cases h with | imp hp _ => exact hp | of_isAtomic hat => cases hat
    have hr : (denote ψ).IsQF := by cases h with | imp _ hp => exact hp | of_isAtomic hat => cases hat
    have ha := matrix_bound φ hl K hk.1
    have hb := matrix_bound ψ hr K hk.2
    simp only [matrix,nodes]
    nlinarith
  | all φ => exact False.elim (BoundedFormula.not_all_isQF (denote φ) h)

def bindAll : {k : Nat} → Data R P k → Data R P 0 × Nat
  | 0, φ => (φ,1)
  | _+1, φ => let r := bindAll (.imp (.all (.imp φ .falsum)) .falsum)
    (r.1,6+r.2)

theorem prefix_value (φ : Data R P k) : denote (bindAll φ).1 = (denote φ).exs := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih _

theorem prefix_cost (φ : Data R P k) : (bindAll φ).2 = 1+6*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bindAll,ih]; omega

theorem prefix_nodes (φ : Data R P k) : nodes (bindAll φ).1 = nodes φ+5*k := by
  induction k with
  | zero => simp only [bindAll,Nat.mul_zero,Nat.add_zero]
  | succ k ih => simp only [bindAll,ih,nodes]; omega

def close (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF) : Data R P 0 × Nat :=
  let a := matrix φ h; let b := bindAll a.1
  (b.1,1+a.2+b.2)

theorem close_value (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF) :
    denote (close φ h).1 = SymbolicReachability.closeColumn (denote φ) := by
  simp only [close,prefix_value,matrix_value,SymbolicReachability.closeColumn]

theorem close_bound (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF)
    (K : Nat) (hk : arity φ ≤ K) : (close φ h).2 ≤ 2+(5+3*K)*nodes φ+6*k := by
  have hm := matrix_bound φ h K hk
  simp only [close,prefix_cost]; omega
theorem matrix_nodes (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF) :
    nodes (matrix φ h).1 = nodes φ := by
  have he := congrArg ExactReachabilitySize.nodes (matrix_value φ h)
  simpa only [denote_nodes,ExactReachabilitySize.nodes_bdRelabel] using he

theorem close_nodes (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF) :
    nodes (close φ h).1 = nodes φ+5*k := by
  simp only [close,prefix_nodes,matrix_nodes]

structure Package (R : Nat → Type) (P : Type) where
  vars : Nat
  body : Data R (P ⊕ Fin vars) 0
  qfree : (denote body).IsQF

def Package.original (A : Package R P) :
    ExistentialFormulaPackage.Package (UniformWordLowering.wordLanguage R) P :=
  ⟨A.vars,denote A.body,A.qfree⟩

def build (A : Package R P) : Data R P 0 × Nat := close A.body A.qfree

theorem build_value (A : Package R P) :
    denote (build A).1 = A.original.toFormula := close_value _ _

theorem build_bound (A : Package R P) (K : Nat) (hk : arity A.body ≤ K) :
    (build A).2 ≤ 2+(5+3*K)*nodes A.body+6*A.vars := close_bound _ _ _ hk

theorem build_nodes (A : Package R P) :
    nodes (build A).1 = nodes A.body+5*A.vars := close_nodes _ _
end NSSE.StoredRelationalClosure
