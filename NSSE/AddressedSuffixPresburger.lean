import NSSE.AllAddressedFactorsPresburger
import NSSE.LinearFamilyStatePresburger

/-!
# Presburger state predicates for suffixes from addressed cuts

These are the terminal-endpoint cases needed by split routes.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def initialSuffixWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (offset : Nat) : Word α :=
  family.initial.drop offset ++
    (List.finRange arity).flatMap (family.stageBlock parameters)

noncomputable def validInitialSuffixStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger arity := by
  classical
  exact
    if family.ValidInitialAddress offset
      then NatPresburger.poweredStatePredicateFormula
        (family.dfaStages automaton)
        (automaton.run (family.initial.drop offset))
        predicate
      else .falsum

theorem eval_validInitialSuffixStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.validInitialSuffixStatePredicateFormula automaton
      offset predicate).Eval parameters ↔
      family.ValidInitialAddress offset ∧
        predicate
          (automaton.run (family.initialSuffixWord parameters offset)) := by
  classical
  by_cases hvalid : family.ValidInitialAddress offset
  · rw [validInitialSuffixStatePredicateFormula,
      if_pos hvalid,
      NatPresburger.poweredStatePredicateFormula_correct]
    rw [dfaStages, family.evaluate_dfaStages_aux]
    unfold initialSuffixWord
    have hstage :
        family.stageBlock parameters =
          (fun index =>
            Word.power (family.pump index) (parameters index) ++
              family.separator index) := rfl
    rw [hstage]
    rw [automaton.run_append]
    simp [hvalid]
  · simp [validInitialSuffixStatePredicateFormula,
      hvalid, NatPresburger.Eval]

theorem drop_word_eq_initialSuffixWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (offset : Nat)
    (hvalid : family.ValidInitialAddress offset) :
    (family.word parameters).drop offset =
      family.initialSuffixWord parameters offset := by
  have hdecompose :=
    family.word_eq_initialAddress_decomposition parameters offset
  have hlength :
      (family.initialAddressPrefix offset).length = offset := by
    simp [initialAddressPrefix, ValidInitialAddress,
      Nat.min_eq_left hvalid]
  rw [hdecompose]
  simp only [List.append_assoc]
  rw [List.drop_left' hlength]
  rfl

def separatorSuffixWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat) : Word α :=
  (family.separator index).drop offset ++
    family.blocksAfter parameters index

def separatorSuffixStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    List (PoweredStateStage arity Q) :=
  ((List.finRange arity).drop (index.val + 1)).map
    (family.dfaStage automaton)

theorem evaluate_separatorSuffixStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.separatorSuffixStages automaton index)
        parameters state =
      automaton.runFrom state
        (family.blocksAfter parameters index) := by
  unfold separatorSuffixStages blocksAfter
  exact family.evaluate_dfaStages_aux automaton
    ((List.finRange arity).drop (index.val + 1))
    parameters state

noncomputable def validSeparatorSuffixStatePredicateFormula
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
      then NatPresburger.poweredStatePredicateFormula
        (family.separatorSuffixStages automaton index)
        (automaton.run ((family.separator index).drop offset))
        predicate
      else .falsum

theorem eval_validSeparatorSuffixStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.validSeparatorSuffixStatePredicateFormula automaton
      index offset predicate).Eval parameters ↔
      family.ValidSeparatorAddress index offset ∧
        predicate
          (automaton.run
            (family.separatorSuffixWord parameters index offset)) := by
  classical
  by_cases hvalid : family.ValidSeparatorAddress index offset
  · rw [validSeparatorSuffixStatePredicateFormula,
      if_pos hvalid,
      NatPresburger.poweredStatePredicateFormula_correct,
      family.evaluate_separatorSuffixStages]
    unfold separatorSuffixWord
    rw [automaton.run_append]
    simp [hvalid]
  · simp [validSeparatorSuffixStatePredicateFormula,
      hvalid, NatPresburger.Eval]

theorem drop_word_eq_separatorSuffixWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (hvalid : family.ValidSeparatorAddress index offset) :
    (family.word parameters).drop
        (family.separatorAddressPosition parameters index offset) =
      family.separatorSuffixWord parameters index offset := by
  have hdecompose :=
    family.word_eq_separatorAddress_decomposition
      parameters index offset
  have hlength :=
    family.separatorAddressPrefix_length parameters index
      offset hvalid
  rw [hdecompose]
  simp only [List.append_assoc]
  rw [List.drop_left' hlength]
  rfl

def pumpSuffixWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (remaining offset : Nat) : Word α :=
  (family.pump index).drop offset ++
    Word.power (family.pump index) remaining ++
    family.separator index ++
    family.blocksAfter parameters index

def pumpSuffixStartStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage (arity + 2) Q where
  coordinate := Fin.last (arity + 1)
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def pumpSuffixLaterStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage (arity + 2) Q where
  coordinate := index.castSucc.castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def pumpSuffixStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    List (PoweredStateStage (arity + 2) Q) :=
  [family.pumpSuffixStartStage automaton index] ++
    ((List.finRange arity).drop (index.val + 1)).map
      (family.pumpSuffixLaterStage automaton)

theorem evaluate_pumpSuffixLaterStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (parameters : Fin arity → Nat)
    (startCopy remaining : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map (family.pumpSuffixLaterStage automaton))
        (pumpRemainingValuation parameters startCopy remaining)
        state =
      automaton.runFrom state
        (indices.flatMap (family.stageBlock parameters)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons later indices ih =>
      simp only [List.map_cons, PoweredStateStage.evaluate,
        pumpSuffixLaterStage, List.flatMap_cons, stageBlock]
      rw [pumpRemainingValuation_parameter]
      rw [ih, automaton.runFrom_append,
        automaton.runFrom_append,
        automaton.runFrom_word_power_eq_iterate]

theorem evaluate_pumpSuffixStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (family.pumpSuffixStages automaton index)
        (pumpRemainingValuation parameters startCopy remaining)
        state =
      automaton.runFrom state
        (Word.power (family.pump index) remaining ++
          family.separator index ++
          family.blocksAfter parameters index) := by
  unfold pumpSuffixStages
  rw [PoweredStateStage.evaluate_append]
  simp only [PoweredStateStage.evaluate, pumpSuffixStartStage]
  rw [pumpRemainingValuation_remaining]
  rw [family.evaluate_pumpSuffixLaterStages]
  unfold blocksAfter
  simp only [automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

def ValidPumpSuffixAddress
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining offset : Nat) : Prop :=
  parameters index = startCopy + 1 + remaining ∧
  offset ≤ (family.pump index).length

def pumpSuffixAddressFormula
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    NatPresburger (arity + 2) :=
  let startCopy : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last arity).castSucc
  let remaining : NatLinearExpr (arity + 2) :=
    .varExpr (Fin.last (arity + 1))
  let count : NatLinearExpr (arity + 2) :=
    .varExpr index.castSucc.castSucc
  if offset ≤ (family.pump index).length
    then .equal count
      (.add (.add startCopy (.const 1)) remaining)
    else .falsum

theorem eval_pumpSuffixAddressFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining offset : Nat) :
    (family.pumpSuffixAddressFormula index offset).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.ValidPumpSuffixAddress parameters index
        startCopy remaining offset := by
  by_cases hoffset : offset ≤ (family.pump index).length
  · simp [pumpSuffixAddressFormula, ValidPumpSuffixAddress,
      hoffset, pumpRemainingValuation, NatPresburger.Eval,
      NatPresburger.extendValuation_castSucc,
      NatPresburger.extendValuation_last]
  · simp only [pumpSuffixAddressFormula, hoffset,
      ↓reduceIte, NatPresburger.Eval, false_iff]
    intro hvalid
    exact (hoffset hvalid.2).elim

noncomputable def validPumpSuffixStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger (arity + 2) :=
  .conj
    (family.pumpSuffixAddressFormula index offset)
    (NatPresburger.poweredStatePredicateFormula
      (family.pumpSuffixStages automaton index)
      (automaton.run ((family.pump index).drop offset))
      predicate)

theorem eval_validPumpSuffixStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining offset : Nat)
    (predicate : Q → Prop) :
    (family.validPumpSuffixStatePredicateFormula automaton
      index offset predicate).Eval
        (pumpRemainingValuation parameters startCopy remaining) ↔
      family.ValidPumpSuffixAddress parameters index
          startCopy remaining offset ∧
        predicate
          (automaton.run
            (family.pumpSuffixWord parameters index
              remaining offset)) := by
  simp only [validPumpSuffixStatePredicateFormula,
    NatPresburger.Eval]
  rw [family.eval_pumpSuffixAddressFormula_iff,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_pumpSuffixStages]
  unfold pumpSuffixWord
  simp only [automaton.run_append,
    automaton.runFrom_append, List.append_assoc]

noncomputable def existsPumpSuffixStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger arity :=
  .existsQ <| .existsQ <|
    family.validPumpSuffixStatePredicateFormula automaton
      index offset predicate

theorem drop_word_eq_pumpSuffixWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining offset : Nat)
    (hvalid :
      family.ValidPumpSuffixAddress parameters index
        startCopy remaining offset) :
    (family.word parameters).drop
        (family.addressPosition parameters index startCopy offset) =
      family.pumpSuffixWord parameters index remaining offset := by
  have hpumpAddress :
      family.ValidPumpAddress parameters index startCopy offset := by
    exact ⟨by rw [hvalid.1]; omega, hvalid.2⟩
  have hdecompose :
      family.word parameters =
        family.addressPrefix parameters index startCopy offset ++
          family.pumpSuffixWord parameters index remaining offset := by
    rw [family.word_eq_stagePrefix_decomposition
      parameters index]
    unfold stagePrefix
    rw [family.blocksBefore_eq_precedingWord]
    rw [power_eq_addressed_suffix_decomposition
      (family.pump index) (parameters index)
      startCopy remaining offset hvalid.1]
    unfold addressPrefix pumpSuffixWord
    have hpreceding :
        ((List.finRange arity).filter
          (fun earlier => earlier < index)).flatMap
            (fun earlier =>
              Word.power (family.pump earlier)
                  (parameters earlier) ++
                family.separator earlier) =
          family.precedingWord parameters index := rfl
    rw [hpreceding]
    simp only [List.append_assoc]
  have hlength :=
    family.addressPrefix_length parameters index
      startCopy offset hpumpAddress.2
  rw [hdecompose, List.drop_left' hlength]

theorem eval_existsPumpSuffixStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.existsPumpSuffixStatePredicateFormula automaton
      index offset predicate).Eval parameters ↔
      ∃ startCopy,
        family.ValidPumpAddress parameters index startCopy offset ∧
          predicate
            (automaton.run
              ((family.word parameters).drop
                (family.addressPosition parameters index
                  startCopy offset))) := by
  simp only [existsPumpSuffixStatePredicateFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨startCopy, remaining, heval⟩
    obtain ⟨hvalid, hpredicate⟩ :=
      (family.eval_validPumpSuffixStatePredicateFormula_iff
        automaton parameters index startCopy remaining
        offset predicate).1 heval
    have hpump :
        family.ValidPumpAddress parameters index startCopy offset :=
      ⟨by rw [hvalid.1]; omega, hvalid.2⟩
    refine ⟨startCopy, hpump, ?_⟩
    rw [family.drop_word_eq_pumpSuffixWord parameters index
      startCopy remaining offset hvalid]
    exact hpredicate
  · rintro ⟨startCopy, hpump, hpredicate⟩
    let remaining := parameters index - (startCopy + 1)
    have hvalid :
        family.ValidPumpSuffixAddress parameters index
          startCopy remaining offset := by
      have hcopy := hpump.1
      exact ⟨by
        dsimp [remaining]
        omega, hpump.2⟩
    refine ⟨startCopy, remaining, ?_⟩
    apply
      (family.eval_validPumpSuffixStatePredicateFormula_iff
        automaton parameters index startCopy remaining
        offset predicate).2
    refine ⟨hvalid, ?_⟩
    rw [← family.drop_word_eq_pumpSuffixWord parameters index
      startCopy remaining offset hvalid]
    exact hpredicate

end LinearWordFamily

end NSSE
