import NSSE.CountedShapeTransition
import NSSE.CountedFiniteModelConstruction

/-! Eager expansion with counted label and transition implementations.
Support materialization, input child lookup and bit/allocation remain excluded. -/
namespace NSSE.CountedShapeExpansion
open SubtypeConstraints FiniteSubtypeTrees FiniteSubtypeSmallModel
variable {n d : Nat}

def expand (φ : Constraints n d) : Nat → List (Fin n) → List (Fin n) → Tree d × Nat
  | 0, _, _ => (.bot,1)
  | k+1, L, U =>
    let l := CountedShapeLabel.label φ L U
    match l.1 with
    | .bot => (.bot,1+l.2)
    | .top => (.top,1+l.2)
    | .node =>
      let children := List.ofFn (fun i =>
        let t := CountedShapeTransition.next φ L U i
        let r := expand φ k t.1.1 t.1.2
        (r.1,1+t.2+r.2))
      (.node (fun i => (children[i.val]'(by simp [children])).1),
        1+l.2+(children.map (fun r => 2+r.2)).sum)

theorem value (φ : Constraints n d) (k : Nat) (L U : List (Fin n)) :
    (expand φ k L U).1 = FiniteTreeGrammar.unfold (SubtypeShapeGrammar.grammar φ)
      k (L.toFinset,U.toFinset) := by
  induction k generalizing L U with
  | zero => rfl
  | succ k ih =>
    have hl := CountedShapeLabel.value φ L U
    cases he : (CountedShapeLabel.label φ L U).1 with
    | bot => simp [expand, he, FiniteTreeGrammar.unfold, ← hl, he]
    | top => simp [expand, he, FiniteTreeGrammar.unfold, ← hl, he]
    | node =>
      simp only [expand, he, FiniteTreeGrammar.unfold, ← hl]
      congr 1
      funext i
      simp only [List.getElem_ofFn]
      rw [ih, CountedShapeTransition.next_value]

def labelBudget (φ : Constraints n d) :=
  6+(φ.lower.length+φ.upper.length+φ.bot.length)*(2+n*(1+n))
def nextBudget (φ : Constraints n d) :=
  1+CountedShapeTransition.stepBudget φ φ.lower.length+
    CountedShapeTransition.stepBudget φ φ.upper.length
def localBudget (φ : Constraints n d) := 1+labelBudget φ+d*(3+nextBudget φ)
def budget (φ : Constraints n d) : Nat → Nat
  | 0 => 1
  | k+1 => localBudget φ+d*budget φ k

theorem bound (φ : Constraints n d) (k : Nat) (L U : List (Fin n))
    (hL : L.length ≤ n) (hU : U.length ≤ n) : (expand φ k L U).2 ≤ budget φ k := by
  induction k generalizing L U with
  | zero => rfl
  | succ k ih =>
    have hl := CountedShapeLabel.bound φ L U hL hU
    cases he : (CountedShapeLabel.label φ L U).1 with
    | bot => simp only [expand, he, budget, localBudget, labelBudget]; omega
    | top => simp only [expand, he, budget, localBudget, labelBudget]; omega
    | node =>
      have hc (i : Fin d) :
          2+(1+(CountedShapeTransition.next φ L U i).2+
            (expand φ k (CountedShapeTransition.next φ L U i).1.1
              (CountedShapeTransition.next φ L U i).1.2).2) ≤ 3+nextBudget φ+budget φ k := by
        have ht := CountedShapeTransition.next_bound φ L U i hL hU
        have hn := CountedShapeTransition.next_lengths φ L U i
        have hr := ih _ _ hn.1 hn.2
        dsimp only [nextBudget]; omega
      have hs := CountedFiniteTreeComparison.sum_bound
        (List.ofFn (fun i =>
          let t := CountedShapeTransition.next φ L U i
          let r := expand φ k t.1.1 t.1.2
          (r.1,1+t.2+r.2))) (fun r => 2+r.2) (3+nextBudget φ+budget φ k)
        (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact hc i)
      simp only [List.length_ofFn] at hs
      simp only [expand, he]
      dsimp only [budget, localBudget, labelBudget]
      nlinarith

theorem budget_power (φ : Constraints n d) (k : Nat) :
    budget φ k ≤ (localBudget φ+d+1)^(k+1) := by
  induction k with
  | zero => simp [budget]
  | succ k ih =>
    have hp : 1 ≤ (localBudget φ+d+1)^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_left d ih
    rw [budget, pow_succ]
    nlinarith

def model (φ : Constraints n d) (x : Fin n) : Tree d × Nat :=
  let s := CountedShapeInitial.initial φ x
  let r := expand φ (stateBound n) s.1.1 s.1.2
  (r.1,1+s.2+r.2)

theorem model_value (φ : Constraints n d) (x : Fin n) :
    (model φ x).1 = FiniteSubtypeSmallModel.model φ x := by
  simp only [model, value, CountedShapeInitial.initial_value, FiniteSubtypeSmallModel.model]

theorem model_bound (φ : Constraints n d) (x : Fin n) :
    (model φ x).2 ≤ 4+2*n*(2+CountedSubtypeSupport.queryBudget φ)+
      (localBudget φ+d+1)^(2^n*2^n+1) := by
  have hi := CountedShapeInitial.initial_bound φ x
  have he := bound φ (stateBound n) (CountedShapeInitial.down φ x).1
    (CountedShapeInitial.up φ x).1 (CountedShapeInitial.down_length φ x)
    (CountedShapeInitial.up_length φ x)
  have hp := he.trans (budget_power φ (stateBound n))
  rw [stateBound_eq] at hp
  simp only [model, CountedShapeInitial.initial, stateBound_eq] at *
  omega
end NSSE.CountedShapeExpansion
