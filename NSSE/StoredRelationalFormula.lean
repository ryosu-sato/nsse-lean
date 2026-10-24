import NSSE.StoredRelationTuple

/-! Explicit function-free syntax with stored tuples of arbitrary finite arity.
The renderer is semantic only. Executable renaming traverses stored lists,
not source tuple closures; relation labels are shared without inspection. -/
namespace NSSE.StoredRelationalFormula
open FirstOrder FirstOrder.Language ExactReachabilitySize
variable {R : Nat → Type} {P Q : Type} {n : Nat}

inductive Data (R : Nat → Type) (P : Type) : Nat → Type
  | falsum {n : Nat} : Data R P n
  | equal {n : Nat} (x y : P ⊕ Fin n) : Data R P n
  | rel {n k : Nat} (r : R k) (args : StoredRelationTuple.Data (P ⊕ Fin n) k) : Data R P n
  | imp {n : Nat} (φ ψ : Data R P n) : Data R P n
  | all {n : Nat} (φ : Data R P (n+1)) : Data R P n

def denote : {n : Nat} → Data R P n → (UniformWordLowering.wordLanguage R).BoundedFormula P n
  | _,.falsum => .falsum
  | _,.equal x y => .equal (.var x) (.var y)
  | _,.rel r args => .rel r (fun i => .var (StoredRelationTuple.read args i).1)
  | _,.imp φ ψ => .imp (denote φ) (denote ψ)
  | _,.all φ => .all (denote φ)

def nodes : {n : Nat} → Data R P n → Nat
  | _,.falsum => 1
  | _,.equal _ _ => 1
  | _,.rel _ _ => 1
  | _,.imp φ ψ => 1+nodes φ+nodes ψ
  | _,.all φ => 1+nodes φ
def arity : {n : Nat} → Data R P n → Nat
  | _,.falsum => 0
  | _,.equal _ _ => 0
  | _,@Data.rel _ _ _ k _ _ => k
  | _,.imp φ ψ => max (arity φ) (arity ψ)
  | _,.all φ => arity φ

theorem denote_nodes (φ : Data R P n) : ExactReachabilitySize.nodes (denote φ) = nodes φ := by
  induction φ <;> simp only [denote,nodes,ExactReachabilitySize.nodes, *]

def name (f : P → Q × Nat) : P ⊕ Fin n → (Q ⊕ Fin n) × Nat
  | .inl p => let r := f p; (.inl r.1,1+r.2)
  | .inr i => (.inr i,1)
theorem name_value (f : P → Q × Nat) (x : P ⊕ Fin n) :
    (name f x).1 = Sum.map (fun p => (f p).1) id x := by cases x <;> rfl
theorem name_bound (f : P → Q × Nat) (b : Nat) (hf : ∀ p, (f p).2 ≤ b) (x : P ⊕ Fin n) :
    (name f x).2 ≤ 1+b := by
  cases x with
  | inl p => exact Nat.add_le_add_left (hf p) 1
  | inr i => simp only [name]; omega

def rename (f : P → Q × Nat) : {n : Nat} → Data R P n → Data R Q n × Nat
  | _,.falsum => (.falsum,1)
  | _,.equal x y => let a := name f x; let b := name f y
    (.equal a.1 b.1,1+a.2+b.2)
  | _,.rel r args => let a := StoredRelationTuple.map (name f) args
    (.rel r a.1,1+a.2)
  | _,.imp φ ψ => let a := rename f φ; let b := rename f ψ
    (.imp a.1 b.1,1+a.2+b.2)
  | _,.all φ => let a := rename f φ; (.all a.1,1+a.2)

def viewRename (f : P → Q) (φ : (UniformWordLowering.wordLanguage R).BoundedFormula P n) :=
  φ.mapTermRel (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)
theorem rename_value (f : P → Q × Nat) (φ : Data R P n) :
    denote (rename f φ).1 = viewRename (fun p => (f p).1) (denote φ) := by
  induction φ with
  | falsum => rfl
  | equal x y => simp only [rename,denote,viewRename,BoundedFormula.mapTermRel,name_value,Term.relabel]
  | rel r args =>
    simp only [rename,denote,viewRename,BoundedFormula.mapTermRel]
    congr 1
    funext i
    simp only [StoredRelationTuple.map_read,name_value,Term.relabel]
  | imp φ ψ ihφ ihψ => simp only [rename,denote,viewRename,BoundedFormula.mapTermRel] at *; rw [ihφ,ihψ]
  | all φ ih => simp only [rename,denote,viewRename,BoundedFormula.mapTermRel] at *; rw [ih]; rfl

theorem viewRename_cast (f : P → Q) (φ : (UniformWordLowering.wordLanguage R).BoundedFormula P n) :
    (viewRename f φ).castLE (Nat.zero_add n).symm.le = φ.relabel (Sum.inl ∘ f) := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [viewRename,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      Term.relabel_relabel,StoredFormulaRelabel.names_cast,BoundedFormula.relabel]
  | rel r ts =>
    simp only [viewRename,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      Function.comp_apply,Term.relabel_relabel,StoredFormulaRelabel.names_cast,BoundedFormula.relabel]
    congr 1
    funext i
    simp only [Function.comp_apply,Term.relabel_relabel,StoredFormulaRelabel.names_cast]
  | imp φ ψ ihφ ihψ =>
    simp only [viewRename,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      BoundedFormula.relabel_imp] at *
    rw [ihφ,ihψ]
  | all φ ih =>
    simp only [viewRename,BoundedFormula.mapTermRel,BoundedFormula.castLE,
      BoundedFormula.relabel_all,id_eq] at *
    rw [ih]

theorem formula_value (f : P → Q × Nat) (φ : Data R P 0) :
    denote (rename f φ).1 = Formula.relabel (fun p => (f p).1) (denote φ) := by
  rw [rename_value]
  simpa only [BoundedFormula.castLE_rfl,Formula.relabel] using viewRename_cast (fun p => (f p).1) (denote φ)

def weight (K b : Nat) := 3+2*b+K*(2+b)
theorem rename_bound (f : P → Q × Nat) (b K : Nat) (hf : ∀ p, (f p).2 ≤ b)
    (φ : Data R P n) (hk : arity φ ≤ K) : (rename f φ).2 ≤ weight K b*nodes φ := by
  induction φ with
  | falsum => simp only [rename,nodes,Nat.mul_one,weight]; omega
  | equal x y =>
    have hx := name_bound f b hf x; have hy := name_bound f b hf y
    simp only [rename,nodes,Nat.mul_one,weight]; omega
  | @rel n k r args =>
    have ha := StoredRelationTuple.map_bound (name f) args (1+b) (name_bound f b hf)
    simp only [show 1+(1+b)=2+b by omega] at ha
    have hm := Nat.mul_le_mul_right (2+b) hk
    simp only [rename,nodes,Nat.mul_one,weight]
    simp only [arity] at hm
    omega
  | imp φ ψ ihφ ihψ =>
    simp only [arity,max_le_iff] at hk
    have ha := ihφ hk.1; have hb := ihψ hk.2
    have hw : 1 ≤ weight K b := by unfold weight; omega
    simp only [rename,nodes]; nlinarith
  | all φ ih =>
    have ha := ih hk
    have hw : 1 ≤ weight K b := by unfold weight; omega
    simp only [rename,nodes]; nlinarith

theorem rename_nodes (f : P → Q × Nat) (φ : Data R P n) : nodes (rename f φ).1 = nodes φ := by
  induction φ <;> simp only [rename,nodes, *]
theorem rename_arity (f : P → Q × Nat) (φ : Data R P n) : arity (rename f φ).1 = arity φ := by
  induction φ <;> simp only [rename,arity, *]
end NSSE.StoredRelationalFormula
