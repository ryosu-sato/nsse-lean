import NSSE.AddressedAutomataConditions

/-!
# DFA acceptance of a factor spanning copies of one pumped word

For two cuts in the same powered zone with
`endCopy = startCopy + gap + 1`, the intervening factor is the suffix of
the start copy, followed by `gap` complete copies, followed by the prefix
of the end copy. Its DFA acceptance and address legality are Presburger.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def samePumpFactorWord
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (gap startOffset endOffset : Nat) : Word α :=
  (family.pump index).drop startOffset ++
    Word.power (family.pump index) gap ++
    (family.pump index).take endOffset

def samePumpFactorStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (endOffset : Nat)
    (gapCoordinate : Fin variableCount) :
    PoweredStateStage variableCount Q where
  coordinate := gapCoordinate
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state
      ((family.pump index).take endOffset)

noncomputable def samePumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat)
    (gapCoordinate : Fin variableCount) :
    NatPresburger variableCount :=
  NatPresburger.poweredStatePredicateFormula
    [family.samePumpFactorStage automaton index
      endOffset gapCoordinate]
    (automaton.run
      ((family.pump index).drop startOffset))
    automaton.accept

theorem eval_samePumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat)
    (gapCoordinate : Fin variableCount)
    (valuation : Fin variableCount → Nat) :
    (family.samePumpFactorAcceptanceFormula automaton index
      startOffset endOffset gapCoordinate).Eval valuation ↔
      automaton.Accepts
        (family.samePumpFactorWord index
          (valuation gapCoordinate) startOffset endOffset) := by
  rw [samePumpFactorAcceptanceFormula,
    NatPresburger.poweredStatePredicateFormula_correct]
  simp only [PoweredStateStage.evaluate,
    samePumpFactorStage]
  unfold DFA.Accepts samePumpFactorWord
  have hmiddle :
      automaton.run
          ((family.pump index).drop startOffset ++
            Word.power (family.pump index)
              (valuation gapCoordinate)) =
        ((fun state =>
          automaton.runFrom state (family.pump index))^[
            valuation gapCoordinate])
          (automaton.run
            ((family.pump index).drop startOffset)) := by
    rw [automaton.run_append,
      automaton.runFrom_word_power_eq_iterate]
  rw [automaton.run_append, hmiddle]

def samePumpGapValuation
    (parameters : Fin arity → Nat)
    (startCopy gap : Nat) :
    Fin (arity + 2) → Nat :=
  NatPresburger.extendValuation
    (NatPresburger.extendValuation parameters startCopy) gap

def samePumpAddressPairFormula
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  let startCopy : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last arity).castSucc
  let gap : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last (arity + 1))
  let count : NatLinearExpr (arity + 2) :=
    .varExpr index.castSucc.castSucc
  .conj
    (.lessEqual
      (.add (.add startCopy gap) (.const 2))
      count)
    (if startOffset ≤ (family.pump index).length ∧
        endOffset ≤ (family.pump index).length
      then NatPresburger.truth
      else .falsum)

def ValidSamePumpAddressPair
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) : Prop :=
  startCopy + gap + 1 < parameters index ∧
  startOffset ≤ (family.pump index).length ∧
  endOffset ≤ (family.pump index).length

theorem samePumpFactorWord_length
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (gap startOffset endOffset : Nat)
    (hendOffset :
      endOffset ≤ (family.pump index).length) :
    (family.samePumpFactorWord index gap
        startOffset endOffset).length =
      ((family.pump index).length - startOffset) +
        gap * (family.pump index).length + endOffset := by
  simp [samePumpFactorWord, Word.power_length,
    Nat.min_eq_left hendOffset, Nat.add_assoc]

theorem samePump_addressPosition_difference
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat)
    (hstartOffset :
      startOffset ≤ (family.pump index).length)
    (hendOffset :
      endOffset ≤ (family.pump index).length) :
    family.addressPosition parameters index
          (startCopy + gap + 1) endOffset -
        family.addressPosition parameters index
          startCopy startOffset =
      (family.samePumpFactorWord index gap
        startOffset endOffset).length := by
  have hsum :
      family.addressPosition parameters index
          (startCopy + gap + 1) endOffset =
        family.addressPosition parameters index
            startCopy startOffset +
          (family.samePumpFactorWord index gap
            startOffset endOffset).length := by
    rw [family.samePumpFactorWord_length index gap
      startOffset endOffset hendOffset]
    unfold addressPosition
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  rw [hsum, Nat.add_sub_cancel_left]

theorem eval_samePumpAddressPairFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) :
    (family.samePumpAddressPairFormula index
      startOffset endOffset).Eval
        (samePumpGapValuation parameters startCopy gap) ↔
      family.ValidSamePumpAddressPair parameters index
        startCopy gap startOffset endOffset := by
  classical
  simp only [samePumpAddressPairFormula,
    NatPresburger.Eval, NatLinearExpr.eval_add,
    NatLinearExpr.eval_const, NatLinearExpr.eval_variable,
    samePumpGapValuation,
    NatPresburger.extendValuation_last,
    NatPresburger.extendValuation_castSucc,
    ValidSamePumpAddressPair, NatPresburger.truth]
  by_cases hoffsets :
      startOffset ≤ (family.pump index).length ∧
        endOffset ≤ (family.pump index).length
  · simp [hoffsets, NatPresburger.Eval]
    omega
  · simp [hoffsets, NatPresburger.Eval]

noncomputable def validSamePumpFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (startOffset endOffset : Nat) :
    NatPresburger (arity + 2) :=
  .conj
    (family.samePumpAddressPairFormula index
      startOffset endOffset)
    (family.samePumpFactorAcceptanceFormula automaton index
      startOffset endOffset (Fin.last (arity + 1)))

theorem eval_validSamePumpFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy gap startOffset endOffset : Nat) :
    (family.validSamePumpFactorAcceptanceFormula automaton
      index startOffset endOffset).Eval
        (samePumpGapValuation parameters startCopy gap) ↔
      family.ValidSamePumpAddressPair parameters index
          startCopy gap startOffset endOffset ∧
        automaton.Accepts
          (family.samePumpFactorWord index gap
            startOffset endOffset) := by
  simp only [validSamePumpFactorAcceptanceFormula,
    NatPresburger.Eval]
  rw [family.eval_samePumpAddressPairFormula_iff,
    family.eval_samePumpFactorAcceptanceFormula_iff]
  simp [samePumpGapValuation]

end LinearWordFamily

end NSSE
