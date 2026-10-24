import NSSE.StoredFiniteTree
import NSSE.CountedModelDepth
import NSSE.CountedFiniteModelConstruction

namespace NSSE.ListShapeExpansion
open StoredSubtypeInput FiniteSubtypeSmallModel
open StoredFiniteTree (Tree denote WellFormed)
variable {n d : Nat}

def expand (I : Input n d) : Nat → List (Fin n) → List (Fin n) → Tree × Nat
  | 0, _, _ => (.bot,1)
  | k+1, L, U =>
    let l := StoredShapeLabel.label I L U
    match l.1 with
    | .bot => (.bot,1+l.2)
    | .top => (.top,1+l.2)
    | .node =>
      let children := CountedFinEnumeration.tabulate d (fun i =>
        let t := StoredShapeTransition.next I L U i
        let r := expand I k t.1.1 t.1.2
        (r.1,1+t.2+r.2))
      (.node children.1,2+l.2+children.2)

theorem value (I : Input n d) (k : Nat) (L U : List (Fin n)) :
    denote d (expand I k L U).1 = FiniteTreeGrammar.unfold (SubtypeShapeGrammar.grammar I.denote)
      k (L.toFinset,U.toFinset) := by
  induction k generalizing L U with
  | zero => simp [expand,denote,FiniteTreeGrammar.unfold]
  | succ k ih =>
    have hl := StoredShapeLabel.value I L U
    cases he : (StoredShapeLabel.label I L U).1 with
    | bot => simp [expand, he, denote, FiniteTreeGrammar.unfold, ← hl, he]
    | top => simp [expand, he, denote, FiniteTreeGrammar.unfold, ← hl, he]
    | node =>
      simp only [expand, he, denote, FiniteTreeGrammar.unfold, ← hl]
      congr 1
      funext i
      simp [denote,CountedFinEnumeration.tabulate_value,List.getElem?_eq_getElem,List.getElem_ofFn]
      rw [ih,StoredShapeTransition.next_value]

theorem wellFormed (I : Input n d) (k : Nat) (L U : List (Fin n)) :
    WellFormed d (expand I k L U).1 := by
  induction k generalizing L U with
  | zero => simp [expand,WellFormed]
  | succ k ih =>
    cases he : (StoredShapeLabel.label I L U).1 with
    | bot => simp [expand,he,WellFormed]
    | top => simp [expand,he,WellFormed]
    | node =>
      simp only [expand,he,CountedFinEnumeration.tabulate_value,WellFormed,List.length_ofFn]
      refine ⟨trivial,?_⟩
      intro t ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      exact ih _ _
def labelBudget (I : Input n d) :=
  6+(I.lower.length+I.upper.length+I.bot.length)*(2+n*(1+n))
def nextBudget (I : Input n d) :=
  1+StoredShapeTransition.stepBudget I I.lower.length+
    StoredShapeTransition.stepBudget I I.upper.length
def localBudget (I : Input n d) := 4+labelBudget I+(d+1)^2+d*(2+nextBudget I)
def budget (I : Input n d) : Nat → Nat
  | 0 => 1
  | k+1 => localBudget I+d*budget I k

theorem bound (I : Input n d) (k : Nat) (L U : List (Fin n))
    (hL : L.length ≤ n) (hU : U.length ≤ n) : (expand I k L U).2 ≤ budget I k := by
  induction k generalizing L U with
  | zero => rfl
  | succ k ih =>
    have hl := StoredShapeLabel.bound I L U hL hU
    cases he : (StoredShapeLabel.label I L U).1 with
    | bot => simp only [expand, he, budget, localBudget, labelBudget]; omega
    | top => simp only [expand, he, budget, localBudget, labelBudget]; omega
    | node =>
      have hc (i : Fin d) :
          1+(StoredShapeTransition.next I L U i).2+
            (expand I k (StoredShapeTransition.next I L U i).1.1
              (StoredShapeTransition.next I L U i).1.2).2 ≤ 1+nextBudget I+budget I k := by
        have ht := StoredShapeTransition.next_bound I L U i hL hU
        have hn := StoredShapeTransition.next_lengths I L U i
        have hr := ih _ _ hn.1 hn.2
        dsimp only [nextBudget]; omega
      have hs := CountedFinEnumeration.tabulate_bound d (fun i =>
        let t := StoredShapeTransition.next I L U i
        let r := expand I k t.1.1 t.1.2
        (r.1,1+t.2+r.2)) (1+nextBudget I+budget I k) hc
      simp only [expand,he]
      dsimp only [budget,localBudget,labelBudget]
      nlinarith

theorem budget_power (I : Input n d) (k : Nat) :
    budget I k ≤ (localBudget I+d+1)^(k+1) := by
  induction k with
  | zero => simp [budget]
  | succ k ih =>
    have hp : 1 ≤ (localBudget I+d+1)^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_left d ih
    rw [budget, pow_succ]
    nlinarith

def model (I : Input n d) (x : Fin n) : Tree × Nat :=
  let s := StoredShapeInitial.initial I x
  let k := CountedModelDepth.depth n
  let r := expand I k.1 s.1.1 s.1.2
  (r.1,2+s.2+k.2+r.2)

theorem model_value (I : Input n d) (x : Fin n) :
    denote d (model I x).1 = FiniteSubtypeSmallModel.model I.denote x := by
  simp only [model, CountedModelDepth.value, value, StoredShapeInitial.value, FiniteSubtypeSmallModel.model]

theorem model_bound (I : Input n d) (x : Fin n) :
    (model I x).2 ≤ 3+2*StoredShapeInitial.seedBudget I+CountedModelDepth.budget n+
      (localBudget I+d+1)^(2^n*2^n+1) := by
  have hi := StoredShapeInitial.bound I x
  have hn := StoredShapeInitial.lengths I x
  have he := bound I (stateBound n) (StoredShapeInitial.initial I x).1.1
    (StoredShapeInitial.initial I x).1.2 hn.1 hn.2
  have hp := he.trans (budget_power I (stateBound n))
  rw [stateBound_eq] at hp
  simp only [model,CountedModelDepth.value,CountedModelDepth.cost,stateBound_eq]
  omega

theorem model_wellFormed (I : Input n d) (x : Fin n) : WellFormed d (model I x).1 :=
  wellFormed I _ _ _
end NSSE.ListShapeExpansion
