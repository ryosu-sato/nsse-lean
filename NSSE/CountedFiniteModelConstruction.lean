import NSSE.CountedFiniteTreeComparison

/-! Eager finite unfolding stores recursively constructed children in a list.
Counts expansion and child-list cells, with label/transition calls counted
as one each. Their implementations and bit/allocation costs remain separate. -/
namespace NSSE.CountedFiniteModelConstruction
open FiniteSubtypeTrees FiniteTreeGrammar FiniteSubtypeSmallModel
variable {S : Type*} {d : Nat}

def expand (G : Grammar S d) : Nat → S → Tree d × Nat
  | 0, _ => (.bot,1)
  | k+1, s => match G.label s with
    | .bot => (.bot,2)
    | .top => (.top,2)
    | .node =>
      let children := List.ofFn (fun i => expand G k (G.next s i))
      (.node (fun i => (children[i.val]'(by simp [children])).1),
        2+(children.map (fun c => 3+c.2)).sum)

theorem value (G : Grammar S d) (k : Nat) (s : S) :
    (expand G k s).1 = unfold G k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases he : G.label s <;> simp [expand, unfold, he, ih]

def budget (d : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => 2+d*(3+budget d k)

theorem budget_two (k : Nat) : 2 ≤ budget d (k+1) := by
  simp only [budget]; omega

theorem bound (G : Grammar S d) (k : Nat) (s : S) :
    (expand G k s).2 ≤ budget d k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases he : G.label s with
    | bot => simpa only [expand, he] using budget_two (d := d) k
    | top => simpa only [expand, he] using budget_two (d := d) k
    | node =>
      have hs := CountedFiniteTreeComparison.sum_bound
        (List.ofFn (fun i => expand G k (G.next s i))) (fun c => 3+c.2)
        (3+budget d k) (by
          intro c hc
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
          exact Nat.add_le_add_left (ih (G.next s i)) 3)
      simpa only [expand, he, List.length_ofFn, budget] using Nat.add_le_add_left hs 2

theorem budget_power (k : Nat) : budget d k ≤ (4*d+3)^(k+1) := by
  induction k with
  | zero => simp [budget]
  | succ k ih =>
    have hp : 1 ≤ (4*d+3)^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_left d ih
    rw [budget, pow_succ]
    nlinarith

/-- The original input alone determines the constructed model. -/
def model (φ : SubtypeConstraints.Constraints n d) (x : Fin n) : Tree d × Nat :=
  expand (SubtypeShapeGrammar.grammar φ) (stateBound n) (SubtypeShapeGrammar.initial φ x)

theorem model_value (φ : SubtypeConstraints.Constraints n d) (x : Fin n) :
    (model φ x).1 = FiniteSubtypeSmallModel.model φ x := value _ _ _

theorem model_bound (φ : SubtypeConstraints.Constraints n d) (x : Fin n) :
    (model φ x).2 ≤ (4*d+3)^(2^n*2^n+1) := by
  have h := (bound (SubtypeShapeGrammar.grammar φ) (stateBound n)
    (SubtypeShapeGrammar.initial φ x)).trans (budget_power (d := d) (stateBound n))
  simpa only [model, stateBound_eq] using h
end NSSE.CountedFiniteModelConstruction
