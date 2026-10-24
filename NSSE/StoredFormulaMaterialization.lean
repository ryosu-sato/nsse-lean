import NSSE.StoredRelationTransport

/-! Materialize all relation occurrences, then evaluate concrete tables. -/
namespace NSSE.StoredFormulaMaterialization
open FirstOrder FirstOrder.Language StoredRelationalFormula FiniteValuationLookup
variable {R : Nat → Type} {d m n : Nat}
abbrev Tables (d k : Nat) := StoredFiniteRelations.Relation d (d^k) k

def interpreter : StoredRelationalEvaluation.Interpreter (Tables d) d :=
  fun k => StoredFiniteRelations.interpret (t := d^k) k

def label (src : StoredRelationalEvaluation.Interpreter R d) (k : Nat) (r : R k) : Tables d k × Nat :=
  StoredRelationMaterialization.build (src k r)
def build (src : StoredRelationalEvaluation.Interpreter R d) (φ : Data R (Fin m) n) :=
  StoredRelationTransport.build (label src) φ

theorem label_correct (src : StoredRelationalEvaluation.Interpreter R d) (k : Nat) (r : R k)
    (xs : StoredRelationTuple.Data (Fin d) k) :
    (interpreter k (label src k r).1 xs).1 = (src k r xs).1 :=
  StoredRelationMaterialization.correct _ _

def labelBudget (d K c : Nat) := 4+(d+1)^2+10*(K+1)*(d+1)^(K+1)+(d+1)^K*(3+c)
theorem label_bound (src : StoredRelationalEvaluation.Interpreter R d) (K c k : Nat)
    (hk : k ≤ K) (hc : ∀ k, k ≤ K → ∀ r xs, (src k r xs).2 ≤ c) (r : R k) :
    (label src k r).2 ≤ labelBudget d K c := by
  have h := StoredRelationMaterialization.exponential_bound (src k r) c (hc k hk r)
  apply h.trans
  unfold labelBudget
  have hp : d^k ≤ (d+1)^K :=
    (Nat.pow_le_pow_left (Nat.le_succ d) k).trans (Nat.pow_le_pow_right (by omega) hk)
  have hq : (d+1)^(k+1) ≤ (d+1)^(K+1) := Nat.pow_le_pow_right (by omega) (by omega)
  gcongr

theorem build_bound (src : StoredRelationalEvaluation.Interpreter R d) (φ : Data R (Fin m) n) (K c : Nat)
    (hc : ∀ k, k ≤ K → ∀ r xs, (src k r xs).2 ≤ c) (hk : arity φ ≤ K) :
    (build src φ).2 ≤ (1+labelBudget d K c)*nodes φ :=
  StoredRelationTransport.bound (label src) φ K _ (fun k hk => label_bound src K c k hk hc) hk

def relationBudget (d K : Nat) := 2+(d+1)^K*(3+K*(2+d))
theorem interpreter_bound (K k : Nat) (hk : k ≤ K) (r : Tables d k)
    (xs : StoredRelationTuple.Data (Fin d) k) : (interpreter k r xs).2 ≤ relationBudget d K := by
  have h := StoredFiniteRelations.interpret_bound K hk r xs
  apply h.trans
  unfold StoredFiniteRelations.budget relationBudget
  have hp : d^k ≤ (d+1)^K :=
    (Nat.pow_le_pow_left (Nat.le_succ d) k).trans (Nat.pow_le_pow_right (by omega) hk)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hp) 2

def decide (src : StoredRelationalEvaluation.Interpreter R d) (φ : Data R (Fin m) 0) (ps : Values d m) : Bool × Nat :=
  let a := build src φ
  let b := StoredRelationalEvaluation.decideFormula interpreter a.1 ps
  (b.1,1+a.2+b.2)
theorem decide_value (src : StoredRelationalEvaluation.Interpreter R d) (φ : Data R (Fin m) 0) (ps : Values d m) :
    (decide src φ ps).1 = (StoredRelationalEvaluation.decideFormula src φ ps).1 :=
  StoredRelationTransport.decide_value (label src) src interpreter (label_correct src) φ ps

theorem decide_correct [(UniformWordLowering.wordLanguage R).Structure (Fin d)]
    (src : StoredRelationalEvaluation.Interpreter R d)
    (hc : ∀ k r xs, (src k r xs).1 = true ↔
      Structure.RelMap (L := UniformWordLowering.wordLanguage R) r (fun i => (StoredRelationTuple.read xs i).1))
    (φ : Data R (Fin m) 0) (ps : Values d m) :
    (decide src φ ps).1 = true ↔ Formula.Realize (denote φ) ps.meaning := by
  rw [decide_value]
  exact StoredRelationalEvaluation.decide_correct src hc φ ps

theorem decide_bound (src : StoredRelationalEvaluation.Interpreter R d) (φ : Data R (Fin m) 0) (ps : Values d m)
    (K c : Nat) (hc : ∀ k, k ≤ K → ∀ r xs, (src k r xs).2 ≤ c) (hk : arity φ ≤ K) :
    (decide src φ ps).2 ≤ 2+(d+1)^2+(1+labelBudget d K c)*nodes φ+
      StoredRelationalEvaluation.weight d m (nodes φ) K d (relationBudget d K)*(nodes φ*(d+1)^nodes φ) := by
  have ha := build_bound src φ K c hc hk
  have hak : arity (build src φ).1 ≤ K := by
    change arity (StoredRelationTransport.build (label src) φ).1 ≤ K
    rw [StoredRelationTransport.arity_value]; exact hk
  have hb := StoredRelationalEvaluation.decide_bound interpreter (build src φ).1 ps K (relationBudget d K)
    (fun k hk => interpreter_bound K k hk) hak
  have hn : nodes (build src φ).1 = nodes φ := StoredRelationTransport.nodes_value _ _
  rw [hn] at hb
  simp only [decide]; omega
end NSSE.StoredFormulaMaterialization
