import NSSE.CrossPumpFactorConcrete

/-!
# Addresses in the fixed zones of a linear word family

The powered-zone address API is complemented by cuts in the initial word
and in a fixed separator.  Their offsets are finite data; only the family
parameters remain Presburger variables.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def initialAddressPrefix
    (family : LinearWordFamily α arity)
    (offset : Nat) : Word α :=
  family.initial.take offset

def ValidInitialAddress
    (family : LinearWordFamily α arity)
    (offset : Nat) : Prop :=
  offset ≤ family.initial.length

def separatorAddressPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat) : Nat :=
  family.pumpEndPosition parameters index + offset

def separatorAddressPrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat) : Word α :=
  family.separatorPrefix parameters index ++
    (family.separator index).take offset

def ValidSeparatorAddress
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) : Prop :=
  offset ≤ (family.separator index).length

theorem separatorAddressPrefix_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (hvalid : family.ValidSeparatorAddress index offset) :
    (family.separatorAddressPrefix parameters index offset).length =
      family.separatorAddressPosition parameters index offset := by
  simp [separatorAddressPrefix, separatorAddressPosition,
    family.separatorPrefix_length, ValidSeparatorAddress,
    Nat.min_eq_left hvalid]

theorem word_eq_initialAddress_decomposition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (offset : Nat) :
    family.word parameters =
      family.initialAddressPrefix offset ++
        family.initial.drop offset ++
        (List.finRange arity).flatMap
          (family.stageBlock parameters) := by
  unfold word initialAddressPrefix
  rw [← List.take_append_drop offset family.initial]
  have hstage :
      family.stageBlock parameters =
        (fun index =>
          Word.power (family.pump index) (parameters index) ++
            family.separator index) := rfl
  rw [hstage]
  simp [List.append_assoc]

theorem word_eq_separatorAddress_decomposition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat) :
    family.word parameters =
      family.separatorAddressPrefix parameters index offset ++
        (family.separator index).drop offset ++
        family.blocksAfter parameters index := by
  rw [family.word_eq_stagePrefix_decomposition parameters index]
  unfold separatorAddressPrefix separatorPrefix
  rw [← List.take_append_drop offset (family.separator index)]
  simp [List.append_assoc]

def separatorAddressFinalStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    PoweredStateStage arity Q where
  coordinate := index
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state
      ((family.separator index).take offset)

def separatorAddressStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    List (PoweredStateStage arity Q) :=
  ((List.finRange arity).filter
      (fun earlier => earlier < index)).map
        (fun earlier =>
          { coordinate := earlier
            powerStep := fun state =>
              automaton.runFrom state (family.pump earlier)
            separatorStep := fun state =>
              automaton.runFrom state
                (family.separator earlier) }) ++
    [family.separatorAddressFinalStage automaton index offset]

theorem evaluate_separatorAddressPrecedingStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (parameters : Fin arity → Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map
          (fun earlier =>
            { coordinate := earlier
              powerStep := fun current =>
                automaton.runFrom current (family.pump earlier)
              separatorStep := fun current =>
                automaton.runFrom current
                  (family.separator earlier) :
              PoweredStateStage arity Q }))
        parameters state =
      automaton.runFrom state
        (indices.flatMap (family.stageBlock parameters)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons, PoweredStateStage.evaluate,
        List.flatMap_cons, stageBlock]
      rw [ih, automaton.runFrom_append,
        automaton.runFrom_append,
        automaton.runFrom_word_power_eq_iterate]

theorem evaluate_separatorAddressStages_from
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.separatorAddressStages automaton index offset)
        parameters state =
      automaton.runFrom state
        (family.precedingWord parameters index ++
          Word.power (family.pump index) (parameters index) ++
          (family.separator index).take offset) := by
  unfold separatorAddressStages
  rw [PoweredStateStage.evaluate_append]
  rw [family.evaluate_separatorAddressPrecedingStages]
  have hstage :
      family.stageBlock parameters =
        (fun earlier =>
          Word.power (family.pump earlier)
              (parameters earlier) ++
            family.separator earlier) := rfl
  rw [hstage]
  have hpreceding :
      ((List.finRange arity).filter
        (fun earlier => earlier < index)).flatMap
          (fun earlier =>
            Word.power (family.pump earlier)
                (parameters earlier) ++
              family.separator earlier) =
        family.precedingWord parameters index := rfl
  rw [hpreceding]
  simp only [PoweredStateStage.evaluate,
    separatorAddressFinalStage]
  simp only [automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

theorem evaluate_separatorAddressStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat) :
    PoweredStateStage.evaluate
        (family.separatorAddressStages automaton index offset)
        parameters (automaton.run family.initial) =
      automaton.run
        (family.separatorAddressPrefix parameters index offset) := by
  rw [family.evaluate_separatorAddressStages_from
    automaton parameters index offset
    (automaton.run family.initial)]
  unfold separatorAddressPrefix separatorPrefix stagePrefix
  rw [family.blocksBefore_eq_precedingWord]
  simp only [precedingWord]
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def separatorAddressStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger arity :=
  NatPresburger.poweredStatePredicateFormula
    (family.separatorAddressStages automaton index offset)
    (automaton.run family.initial) predicate

theorem eval_separatorAddressStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.separatorAddressStatePredicateFormula automaton
      index offset predicate).Eval parameters ↔
      predicate
        (automaton.run
          (family.separatorAddressPrefix parameters
            index offset)) := by
  rw [separatorAddressStatePredicateFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_separatorAddressStages]

noncomputable def validSeparatorAddressStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger arity := by
  classical
  exact
    if family.ValidSeparatorAddress index offset
      then family.separatorAddressStatePredicateFormula
        automaton index offset predicate
      else .falsum

theorem eval_validSeparatorAddressStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.validSeparatorAddressStatePredicateFormula automaton
      index offset predicate).Eval parameters ↔
      family.ValidSeparatorAddress index offset ∧
        predicate
          (automaton.run
            (family.separatorAddressPrefix parameters
              index offset)) := by
  by_cases hvalid : family.ValidSeparatorAddress index offset
  · simp [validSeparatorAddressStatePredicateFormula, hvalid,
      family.eval_separatorAddressStatePredicateFormula_iff]
  · simp [validSeparatorAddressStatePredicateFormula, hvalid,
      NatPresburger.Eval]

noncomputable def validInitialAddressStatePredicateFormula
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger arity := by
  classical
  exact
    if family.ValidInitialAddress offset ∧
        predicate (automaton.run (family.initialAddressPrefix offset))
      then NatPresburger.truth
      else .falsum

theorem eval_validInitialAddressStatePredicateFormula_iff
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.validInitialAddressStatePredicateFormula automaton
      offset predicate).Eval parameters ↔
      family.ValidInitialAddress offset ∧
        predicate
          (automaton.run (family.initialAddressPrefix offset)) := by
  by_cases h :
      family.ValidInitialAddress offset ∧
        predicate
          (automaton.run (family.initialAddressPrefix offset))
  · simp [validInitialAddressStatePredicateFormula, h,
      NatPresburger.truth, NatPresburger.Eval]
  · simp [validInitialAddressStatePredicateFormula, h,
      NatPresburger.Eval]

end LinearWordFamily

end NSSE
