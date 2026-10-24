import NSSE.SamePumpPeriodicWitnessPresburger

/-!
# DFA stage programs under one unused trailing coordinate
-/

namespace NSSE

universe u v

namespace PoweredStateStage

def weaken
    (stage : PoweredStateStage variableCount Q) :
    PoweredStateStage (variableCount + 1) Q where
  coordinate := stage.coordinate.castSucc
  powerStep := stage.powerStep
  separatorStep := stage.separatorStep

@[simp] theorem evaluate_map_weaken
    (stages : List (PoweredStateStage variableCount Q))
    (valuation : Fin variableCount → Nat)
    (bound : Nat)
    (state : Q) :
    evaluate (stages.map weaken)
        (NatPresburger.extendValuation valuation bound) state =
      evaluate stages valuation state := by
  induction stages generalizing state with
  | nil => rfl
  | cons stage stages ih =>
      simp only [List.map_cons, evaluate, weaken,
        NatPresburger.extendValuation_castSucc]
      exact ih _

end PoweredStateStage

end NSSE
