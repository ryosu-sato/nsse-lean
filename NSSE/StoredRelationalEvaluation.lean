import NSSE.StoredRelationalNonempty

/-! Evaluation of stored relational syntax with an explicit counted relation
interpreter. Relation implementation and its counter bound are parameters. -/
namespace NSSE.StoredRelationalEvaluation
open FirstOrder FirstOrder.Language StoredRelationalFormula FiniteValuationLookup
variable {R : Nat → Type} {d m n : Nat}

def name (ps : Values d m) (vs : Values d n) : Fin m ⊕ Fin n → Fin d × Nat
  | .inl i => let r := ps.lookup i; (r.1,1+r.2)
  | .inr i => let r := vs.lookup i; (r.1,1+r.2)
theorem name_value (ps : Values d m) (vs : Values d n) (x : Fin m ⊕ Fin n) :
    (name ps vs x).1 = Sum.elim ps.meaning vs.meaning x := by
  cases x <;> simp only [name,Values.lookup_correct,Sum.elim_inl,Sum.elim_inr]
theorem name_bound (ps : Values d m) (vs : Values d n) (x : Fin m ⊕ Fin n) :
    (name ps vs x).2 ≤ 1+m+n := by
  cases x with
  | inl i => have h := ps.lookup_bound i; simp only [name]; omega
  | inr i => have h := vs.lookup_bound i; simp only [name]; omega

abbrev Interpreter (R : Nat → Type) (d : Nat) :=
  (k : Nat) → R k → StoredRelationTuple.Data (Fin d) k → Bool × Nat

def evaluate (rel : Interpreter R d) (domain : List (Fin d)) (ps : Values d m) :
    {n : Nat} → Data R (Fin m) n → Values d n → Bool × Nat
  | _,.falsum,_ => (false,1)
  | _,.equal x y,vs =>
    let a := name ps vs x; let b := name ps vs y
    let e := equalNat a.1.val b.1.val
    (e.1,1+a.2+b.2+e.2)
  | _,.rel r args,vs =>
    let a := StoredRelationTuple.map (name ps vs) args
    let b := rel _ r a.1
    (b.1,1+a.2+b.2)
  | _,.imp φ ψ,vs =>
    let a := evaluate rel domain ps φ vs; let b := evaluate rel domain ps ψ vs
    (!a.1 || b.1,1+a.2+b.2)
  | _,.all φ,vs =>
    let r := StoredQuantifiedEvaluation.every (fun x =>
      let a := evaluate rel domain ps φ (.snoc vs x); (a.1,1+a.2)) domain
    (r.1,1+r.2)

theorem correct [(UniformWordLowering.wordLanguage R).Structure (Fin d)]
    (rel : Interpreter R d)
    (hr : ∀ k r xs, (rel k r xs).1 = true ↔
      Structure.RelMap (L := UniformWordLowering.wordLanguage R) r (fun i => (StoredRelationTuple.read xs i).1))
    (domain : List (Fin d)) (complete : ∀ x, x ∈ domain) (ps : Values d m)
    (φ : Data R (Fin m) n) (vs : Values d n) :
    (evaluate rel domain ps φ vs).1 = true ↔ (denote φ).Realize ps.meaning vs.meaning := by
  induction φ with
  | falsum => simp [evaluate,denote,BoundedFormula.Realize]
  | equal x y =>
    simp only [evaluate,equalNat_correct,name_value,denote,BoundedFormula.Realize,Term.realize,Fin.ext_iff]
  | rel r args =>
    simp only [evaluate,hr,denote,BoundedFormula.Realize,Term.realize,
      StoredRelationTuple.map_read,name_value]
  | imp φ ψ ihφ ihψ =>
    change ((! (evaluate rel domain ps φ vs).1) || (evaluate rel domain ps ψ vs).1) = true ↔ _
    rw [Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff]
    simp only [denote,BoundedFormula.Realize]
    have hφ := ihφ vs; have hψ := ihψ vs
    tauto
  | all φ ih =>
    simp only [evaluate,StoredQuantifiedEvaluation.every_value,denote,BoundedFormula.Realize]
    constructor
    · intro h x; exact (ih (.snoc vs x)).mp (h x (complete x))
    · intro h x _; exact (ih (.snoc vs x)).mpr (h x)

def weight (d m N K l c : Nat) := 3+2*(m+N)+d+3*l+K*(2+m+N)+c

theorem bound (rel : Interpreter R d) (domain : List (Fin d)) (ps : Values d m)
    (φ : Data R (Fin m) n) (vs : Values d n) (N K c : Nat)
    (hr : ∀ k, k ≤ K → ∀ r xs, (rel k r xs).2 ≤ c)
    (hn : n+nodes φ ≤ N) (hk : arity φ ≤ K) :
    (evaluate rel domain ps φ vs).2 ≤
      weight d m N K domain.length c * CountedFiniteFormulaEvaluation.visits domain.length (denote φ) := by
  induction φ with
  | falsum => simp only [evaluate,denote,CountedFiniteFormulaEvaluation.visits,Nat.mul_one,weight]; omega
  | equal x y =>
    have hx := name_bound ps vs x; have hy := name_bound ps vs y
    have he := equalFin_bound (name ps vs x).1 (name ps vs y).1
    simp only [nodes] at hn
    simp only [evaluate,denote,CountedFiniteFormulaEvaluation.visits,Nat.mul_one,weight]; omega
  | @rel n k r args =>
    have ha := StoredRelationTuple.map_bound (name ps vs) args (1+m+n) (name_bound ps vs)
    have hb := hr k hk r (StoredRelationTuple.map (name ps vs) args).1
    have hn' : n ≤ N := by simp only [nodes] at hn; omega
    have hm : k*(1+(1+m+n)) ≤ K*(2+m+N) := by
      simp only [arity] at hk
      exact Nat.mul_le_mul hk (by omega)
    simp only [evaluate,denote,CountedFiniteFormulaEvaluation.visits,Nat.mul_one,weight]; omega
  | imp φ ψ ihφ ihψ =>
    simp only [nodes] at hn
    simp only [arity,max_le_iff] at hk
    have ha := ihφ vs (by omega) hk.1
    have hb := ihψ vs (by omega) hk.2
    have hw : 1 ≤ weight d m N K domain.length c := by unfold weight; omega
    simp only [evaluate,denote,CountedFiniteFormulaEvaluation.visits]; nlinarith
  | all φ ih =>
    have hh := StoredQuantifiedEvaluation.every_bound (fun x =>
      let a := evaluate rel domain ps φ (.snoc vs x); (a.1,1+a.2)) domain
      (1+weight d m N K domain.length c*CountedFiniteFormulaEvaluation.visits domain.length (denote φ))
      (fun x _ => Nat.add_le_add_left (ih (.snoc vs x) (by simp only [nodes] at hn; omega) hk) 1)
    have hw : 2+3*domain.length ≤ weight d m N K domain.length c := by unfold weight; omega
    simp only [evaluate,denote,CountedFiniteFormulaEvaluation.visits]; nlinarith

def decideFormula (rel : Interpreter R d) (φ : Data R (Fin m) 0) (ps : Values d m) : Bool × Nat :=
  let a := CountedFinEnumeration.enumerate d
  let b := evaluate rel a.1 ps φ .nil
  (b.1,1+a.2+b.2)
theorem decide_correct [(UniformWordLowering.wordLanguage R).Structure (Fin d)]
    (rel : Interpreter R d)
    (hr : ∀ k r xs, (rel k r xs).1 = true ↔ Structure.RelMap (L := UniformWordLowering.wordLanguage R) r (fun i => (StoredRelationTuple.read xs i).1))
    (φ : Data R (Fin m) 0) (ps : Values d m) :
    (decideFormula rel φ ps).1 = true ↔ Formula.Realize (denote φ) ps.meaning := by
  simp only [decideFormula,CountedFinEnumeration.value]
  exact correct rel hr _ (fun x => List.mem_finRange x) ps φ .nil

theorem decide_bound (rel : Interpreter R d) (φ : Data R (Fin m) 0) (ps : Values d m) (K c : Nat)
    (hr : ∀ k, k ≤ K → ∀ r xs, (rel k r xs).2 ≤ c) (hk : arity φ ≤ K) :
    (decideFormula rel φ ps).2 ≤ 1+(d+1)^2+
      weight d m (nodes φ) K d c * (nodes φ*(d+1)^nodes φ) := by
  have he := CountedFinEnumeration.bound d
  have h := bound rel (List.finRange d) ps φ .nil (nodes φ) K c hr (by omega) hk
  simp only [List.length_finRange] at h
  have hv := CountedFiniteFormulaEvaluation.visits_bound d (denote φ)
  rw [denote_nodes] at hv
  have hh := h.trans (Nat.mul_le_mul_left (weight d m (nodes φ) K d c) hv)
  simp only [decideFormula,CountedFinEnumeration.value]; omega
end NSSE.StoredRelationalEvaluation
