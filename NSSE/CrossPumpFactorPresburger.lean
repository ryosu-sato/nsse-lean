import NSSE.SamePumpFactorConcrete

/-!
# DFA acceptance of a factor crossing two powered zones

For fixed stages `startIndex < endIndex`, a factor beginning inside one
copy of the first pump and ending inside one copy of the last pump is
split into a fixed suffix, the remaining first-stage copies, all complete
intermediate stages, the preceding last-stage copies, and a fixed prefix.

The number of remaining first-stage copies is kept as an existential
Presburger coordinate.  Its legality equation is

`parameters startIndex = startCopy + 1 + remaining`.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def crossPumpMiddleIndices
    (startIndex endIndex : Fin arity) : List (Fin arity) :=
  ((List.finRange arity).drop (startIndex.val + 1)).take
    (endIndex.val - (startIndex.val + 1))

def crossPumpFactorWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (remaining endCopy startOffset endOffset : Nat) : Word α :=
  (family.pump startIndex).drop startOffset ++
    Word.power (family.pump startIndex) remaining ++
    family.separator startIndex ++
    (crossPumpMiddleIndices startIndex endIndex).flatMap
      (family.stageBlock parameters) ++
    Word.power (family.pump endIndex) endCopy ++
    (family.pump endIndex).take endOffset

def crossPumpStartStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex : Fin arity)
    (remainingCoordinate : Fin variableCount) :
    PoweredStateStage variableCount Q where
  coordinate := remainingCoordinate
  powerStep := fun state =>
    automaton.runFrom state (family.pump startIndex)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator startIndex)

def crossPumpMiddleStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage (arity + 3) Q where
  coordinate := index.castSucc.castSucc.castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def crossPumpEndStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (endIndex : Fin arity)
    (endOffset : Nat) :
    PoweredStateStage (arity + 3) Q where
  coordinate := (Fin.last (arity + 1)).castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump endIndex)
  separatorStep := fun state =>
    automaton.runFrom state
      ((family.pump endIndex).take endOffset)

def crossPumpFactorStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (endOffset : Nat) :
    List (PoweredStateStage (arity + 3) Q) :=
  [family.crossPumpStartStage automaton startIndex
      (Fin.last (arity + 2))] ++
    (crossPumpMiddleIndices startIndex endIndex).map
      (family.crossPumpMiddleStage automaton) ++
    [family.crossPumpEndStage automaton endIndex endOffset]

def crossPumpValuation
    (parameters : Fin arity → Nat)
    (startCopy remaining endCopy : Nat) :
    Fin (arity + 3) → Nat :=
  NatPresburger.extendValuation
    (NatPresburger.extendValuation
      (NatPresburger.extendValuation parameters startCopy)
      endCopy)
    remaining

def crossPumpEndpointValuation
    (parameters : Fin arity → Nat)
    (startCopy endCopy : Nat) :
    Fin (arity + 2) → Nat :=
  NatPresburger.extendValuation
    (NatPresburger.extendValuation parameters startCopy)
    endCopy

theorem crossPumpValuation_eq_extendEndpoint
    (parameters : Fin arity → Nat)
    (startCopy remaining endCopy : Nat) :
    crossPumpValuation parameters startCopy remaining endCopy =
      NatPresburger.extendValuation
        (crossPumpEndpointValuation parameters startCopy endCopy)
        remaining := rfl

theorem crossPumpValuation_parameter
    (parameters : Fin arity → Nat)
    (startCopy remaining endCopy : Nat)
    (index : Fin arity) :
    crossPumpValuation parameters startCopy remaining endCopy
        index.castSucc.castSucc.castSucc =
      parameters index := by
  simp [crossPumpValuation,
    NatPresburger.extendValuation_castSucc]

theorem crossPumpValuation_remaining
    (parameters : Fin arity → Nat)
    (startCopy remaining endCopy : Nat) :
    crossPumpValuation parameters startCopy remaining endCopy
        (Fin.last (arity + 2)) =
      remaining := by
  simp [crossPumpValuation,
    NatPresburger.extendValuation_last]

theorem crossPumpValuation_endCopy
    (parameters : Fin arity → Nat)
    (startCopy remaining endCopy : Nat) :
    crossPumpValuation parameters startCopy remaining endCopy
        (Fin.last (arity + 1)).castSucc =
      endCopy := by
  simp [crossPumpValuation,
    NatPresburger.extendValuation_castSucc,
    NatPresburger.extendValuation_last]

theorem evaluate_crossPumpMiddleStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (valuation : Fin (arity + 3) → Nat)
    (parameters : Fin arity → Nat)
    (hparameters :
      ∀ index,
        valuation index.castSucc.castSucc.castSucc =
          parameters index)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map
          (family.crossPumpMiddleStage automaton))
        valuation state =
      automaton.runFrom state
        (indices.flatMap (family.stageBlock parameters)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons,
        PoweredStateStage.evaluate, crossPumpMiddleStage,
        List.flatMap_cons, stageBlock]
      rw [hparameters index]
      rw [ih]
      · rw [automaton.runFrom_append,
          automaton.runFrom_append,
          automaton.runFrom_word_power_eq_iterate]

theorem evaluate_crossPumpFactorStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat) :
    PoweredStateStage.evaluate
        (family.crossPumpFactorStages automaton
          startIndex endIndex endOffset)
        (crossPumpValuation parameters
          startCopy remaining endCopy)
        (automaton.run
          ((family.pump startIndex).drop startOffset)) =
      automaton.run
        (family.crossPumpFactorWord parameters
          startIndex endIndex remaining endCopy
          startOffset endOffset) := by
  unfold crossPumpFactorStages
  rw [PoweredStateStage.evaluate_append,
    PoweredStateStage.evaluate_append]
  simp only [PoweredStateStage.evaluate,
    crossPumpStartStage, crossPumpEndStage]
  rw [crossPumpValuation_remaining,
    crossPumpValuation_endCopy]
  rw [family.evaluate_crossPumpMiddleStages
    automaton
    (crossPumpMiddleIndices startIndex endIndex)
    (crossPumpValuation parameters
      startCopy remaining endCopy) parameters]
  · unfold crossPumpFactorWord
    simp only [automaton.run_append,
      automaton.runFrom_append,
      automaton.runFrom_word_power_eq_iterate]
  · intro index
    exact crossPumpValuation_parameter
      parameters startCopy remaining endCopy index

noncomputable def crossPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 3) :=
  NatPresburger.poweredStatePredicateFormula
    (family.crossPumpFactorStages automaton
      startIndex endIndex endOffset)
    (automaton.run
      ((family.pump startIndex).drop startOffset))
    automaton.accept

theorem eval_crossPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat) :
    (family.crossPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (crossPumpValuation parameters
          startCopy remaining endCopy) ↔
      automaton.Accepts
        (family.crossPumpFactorWord parameters
          startIndex endIndex remaining endCopy
          startOffset endOffset) := by
  rw [crossPumpFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_crossPumpFactorStages]
  rfl

def ValidCrossPumpAddressPair
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat) : Prop :=
  startIndex < endIndex ∧
  parameters startIndex = startCopy + 1 + remaining ∧
  endCopy < parameters endIndex ∧
  startOffset ≤ (family.pump startIndex).length ∧
  endOffset ≤ (family.pump endIndex).length

def crossPumpAddressPairFormula
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 3) :=
  let startCopy : NatLinearExpr (arity + 3) :=
    .varExpr (Fin.last arity).castSucc.castSucc
  let remaining : NatLinearExpr (arity + 3) :=
    .varExpr (Fin.last (arity + 2))
  let endCopy : NatLinearExpr (arity + 3) :=
    .varExpr (Fin.last (arity + 1)).castSucc
  let startCount : NatLinearExpr (arity + 3) :=
    .varExpr startIndex.castSucc.castSucc.castSucc
  let endCount : NatLinearExpr (arity + 3) :=
    .varExpr endIndex.castSucc.castSucc.castSucc
  if startIndex < endIndex ∧
      startOffset ≤ (family.pump startIndex).length ∧
      endOffset ≤ (family.pump endIndex).length
    then
      .conj
        (.equal startCount
          (.add (.add startCopy (.const 1)) remaining))
        (.lessEqual (.add endCopy (.const 1)) endCount)
    else .falsum

theorem eval_crossPumpAddressPairFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat) :
    (family.crossPumpAddressPairFormula startIndex endIndex
      startOffset endOffset).Eval
        (crossPumpValuation parameters
          startCopy remaining endCopy) ↔
      family.ValidCrossPumpAddressPair parameters
        startIndex endIndex startCopy remaining endCopy
        startOffset endOffset := by
  by_cases hfixed :
      startIndex < endIndex ∧
      startOffset ≤ (family.pump startIndex).length ∧
      endOffset ≤ (family.pump endIndex).length
  · simp [crossPumpAddressPairFormula,
      ValidCrossPumpAddressPair, hfixed,
      NatPresburger.Eval, crossPumpValuation,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last]
    omega
  · simp only [crossPumpAddressPairFormula, hfixed,
      ↓reduceIte, NatPresburger.Eval, false_iff]
    intro hvalid
    unfold ValidCrossPumpAddressPair at hvalid
    exact (hfixed
      ⟨hvalid.1, hvalid.2.2.2.1,
        hvalid.2.2.2.2⟩).elim

noncomputable def validCrossPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 3) :=
  .conj
    (family.crossPumpAddressPairFormula startIndex endIndex
      startOffset endOffset)
    (family.crossPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset)

theorem eval_validCrossPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy remaining endCopy startOffset endOffset : Nat) :
    (family.validCrossPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset).Eval
        (crossPumpValuation parameters
          startCopy remaining endCopy) ↔
      family.ValidCrossPumpAddressPair parameters
          startIndex endIndex startCopy remaining endCopy
          startOffset endOffset ∧
        automaton.Accepts
          (family.crossPumpFactorWord parameters
            startIndex endIndex remaining endCopy
            startOffset endOffset) := by
  simp only [validCrossPumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  rw [family.eval_crossPumpAddressPairFormula_iff,
    family.eval_crossPumpFactorAcceptanceFormula_iff]

noncomputable def existsRemainingCrossPumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (startIndex endIndex : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  .existsQ
    (family.validCrossPumpFactorAcceptanceFormula automaton
      startIndex endIndex startOffset endOffset)

theorem eval_existsRemainingCrossPumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (startIndex endIndex : Fin arity)
    (startCopy endCopy startOffset endOffset : Nat) :
    (family.existsRemainingCrossPumpFactorAcceptanceFormula
      automaton startIndex endIndex startOffset endOffset).Eval
        (crossPumpEndpointValuation parameters
          startCopy endCopy) ↔
      ∃ remaining,
        family.ValidCrossPumpAddressPair parameters
            startIndex endIndex startCopy remaining endCopy
            startOffset endOffset ∧
          automaton.Accepts
            (family.crossPumpFactorWord parameters
              startIndex endIndex remaining endCopy
              startOffset endOffset) := by
  simp only [existsRemainingCrossPumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨remaining, heval⟩
    refine ⟨remaining, ?_⟩
    apply
      (family.eval_validCrossPumpFactorAcceptanceFormula_iff
        automaton parameters startIndex endIndex startCopy
        remaining endCopy startOffset endOffset).1
    simpa [crossPumpValuation_eq_extendEndpoint] using heval
  · rintro ⟨remaining, hvalid⟩
    refine ⟨remaining, ?_⟩
    have heval :=
      (family.eval_validCrossPumpFactorAcceptanceFormula_iff
        automaton parameters startIndex endIndex startCopy
        remaining endCopy startOffset endOffset).2 hvalid
    simpa [crossPumpValuation_eq_extendEndpoint] using heval

end LinearWordFamily

end NSSE
