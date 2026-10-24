import NSSE.StoredRelationMaterialization

/-! Counted relation-label transport on stored syntax. Tuple lists are shared. -/
namespace NSSE.StoredRelationTransport
open StoredRelationalFormula FiniteValuationLookup
variable {R S : Nat → Type} {P : Type} {d m n : Nat}

def build (f : (k : Nat) → R k → S k × Nat) : {n : Nat} → Data R P n → Data S P n × Nat
  | _,.falsum => (.falsum,1)
  | _,.equal x y => (.equal x y,1)
  | _,.rel r args => let a := f _ r; (.rel a.1 args,1+a.2)
  | _,.imp φ ψ => let a := build f φ; let b := build f ψ; (.imp a.1 b.1,1+a.2+b.2)
  | _,.all φ => let a := build f φ; (.all a.1,1+a.2)
theorem nodes_value (f : (k : Nat) → R k → S k × Nat) (φ : Data R P n) :
    nodes (build f φ).1 = nodes φ := by induction φ <;> simp only [build,nodes, *]
theorem arity_value (f : (k : Nat) → R k → S k × Nat) (φ : Data R P n) :
    arity (build f φ).1 = arity φ := by induction φ <;> simp only [build,arity, *]
theorem bound (f : (k : Nat) → R k → S k × Nat) (φ : Data R P n) (K c : Nat)
    (hc : ∀ k, k ≤ K → ∀ r, (f k r).2 ≤ c) (hk : arity φ ≤ K) :
    (build f φ).2 ≤ (1+c)*nodes φ := by
  induction φ with
  | falsum => simp [build,nodes]
  | equal x y => simp [build,nodes]
  | @rel n k r args => have h := hc k hk r; simp only [build,nodes,Nat.mul_one]; omega
  | imp φ ψ ihφ ihψ =>
    simp only [arity,max_le_iff] at hk
    have ha := ihφ hk.1; have hb := ihψ hk.2
    simp only [build,nodes]; nlinarith
  | all φ ih => have h := ih hk; simp only [build,nodes]; nlinarith

theorem evaluate_value (f : (k : Nat) → R k → S k × Nat)
    (src : StoredRelationalEvaluation.Interpreter R d) (dst : StoredRelationalEvaluation.Interpreter S d)
    (hf : ∀ k r xs, (dst k (f k r).1 xs).1 = (src k r xs).1)
    (domain : List (Fin d)) (ps : Values d m) (φ : Data R (Fin m) n) (vs : Values d n) :
    (StoredRelationalEvaluation.evaluate dst domain ps (build f φ).1 vs).1 =
      (StoredRelationalEvaluation.evaluate src domain ps φ vs).1 := by
  induction φ with
  | falsum => rfl
  | equal x y => rfl
  | rel r args => simp only [build,StoredRelationalEvaluation.evaluate,hf]
  | imp φ ψ ihφ ihψ => simp only [build,StoredRelationalEvaluation.evaluate,ihφ,ihψ]
  | all φ ih =>
    apply Bool.eq_iff_iff.mpr
    simp only [build,StoredRelationalEvaluation.evaluate,StoredQuantifiedEvaluation.every_value,ih]

theorem decide_value (f : (k : Nat) → R k → S k × Nat)
    (src : StoredRelationalEvaluation.Interpreter R d) (dst : StoredRelationalEvaluation.Interpreter S d)
    (hf : ∀ k r xs, (dst k (f k r).1 xs).1 = (src k r xs).1)
    (φ : Data R (Fin m) 0) (ps : Values d m) :
    (StoredRelationalEvaluation.decideFormula dst (build f φ).1 ps).1 =
      (StoredRelationalEvaluation.decideFormula src φ ps).1 := by
  simp only [StoredRelationalEvaluation.decideFormula,evaluate_value f src dst hf]
end NSSE.StoredRelationTransport
