import NSSE.StoredGraphHorn
import NSSE.InitializedHornEvaluation

namespace NSSE.StoredGraphReachability
open StoredProductivityGraph

def decide (G : Data) (q : Nat) : Bool × Nat :=
  let p := StoredGraphHorn.build G
  let r := InitializedHornEvaluation.decide p.1 q
  (r.1,1+p.2+r.2)

theorem value (G : Data) (q : Nat) :
    (decide G q).1 = (StoredGraphHorn.game G).decideWinning q := by
  simp only [decide,InitializedHornEvaluation.value,CountedHornEvaluation.decide_value,
    StoredGraphHorn.value,MaterializedHornProgram.decide_eq,FiniteReachabilityGame.decideWinning]

theorem correct (G : Data) (q : Fin G.count) :
    (decide G q.val).1 = true ↔ (StoredGraphHorn.game G).Winning q.val := by
  rw [value]
  exact FiniteReachabilityGame.decideWinning_correct _ q.val q.isLt

def budget (n : Nat) := 1+StoredGraphHorn.budget n+
  CountedHornEvaluationBound.budget n (n*n) 1+n+2

theorem bound (G : Data) (q : Nat) : (decide G q).2 ≤ budget G.count := by
  have hp := StoredGraphHorn.bound G
  have hr := InitializedHornEvaluation.bound (StoredGraphHorn.build G).1 q 1
    (le_of_eq (StoredGraphHorn.terminals_length G)) (StoredGraphHorn.children_length G)
  have hn := StoredGraphHorn.rules_bound G
  have hc : (StoredGraphHorn.build G).1.count = G.count := rfl
  rw [hc] at hr
  have hm : CountedHornEvaluationBound.budget G.count (StoredGraphHorn.build G).1.rules.length 1 ≤
      CountedHornEvaluationBound.budget G.count (G.count*G.count) 1 := by
    unfold CountedHornEvaluationBound.budget CountedHornEvaluationBound.cellBudget
    gcongr
  simp only [decide,budget]
  omega
theorem game_snapshot {d : Nat} (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    StoredGraphHorn.game (snapshotGame D.automaton.productivityGame) = D.automaton.productivityGame := by
  unfold StoredGraphHorn.game snapshotGame
  congr 1
  · funext q
    by_cases hq : q<D.count <;>
      simp [StoredForwardLookup.get_value,List.getElem?_ofFn,DFA.productivityGame,hq]
  · funext q r
    by_cases hq : q<D.count <;> by_cases hr : r<D.count <;>
      simp [StoredForwardLookup.two,StoredForwardLookup.get_value,List.getElem?_ofFn,
        DFA.productivityGame,hq,hr]

theorem productive_value {d : Nat} (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin D.count) :
    (decide (snapshotGame D.automaton.productivityGame) q.val).1 =
      D.automaton.executableProductive.productive q := by
  rw [value,game_snapshot]
  rfl
end NSSE.StoredGraphReachability
