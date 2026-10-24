import NSSE.ParametrizedPeriodicityPresburger

/-!
# Presburger DFA states at powered-block addresses

For a fixed stage and within-copy offset, the preceding family parameters
and the quantified copy number form one powered-state composition. This
completes the addressed form of Lemma A.0.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def addressedPrecedingStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage (arity + 1) Q where
  coordinate := index.castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def addressedFinalStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    PoweredStateStage (arity + 1) Q where
  coordinate := Fin.last arity
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state
      ((family.pump index).take offset)

def addressedDFAStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    List (PoweredStateStage (arity + 1) Q) :=
  ((List.finRange arity).filter
      (fun earlier => earlier < index)).map
        (family.addressedPrecedingStage automaton) ++
    [family.addressedFinalStage automaton index offset]

theorem evaluate_addressedPrecedingStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (parameters : Fin arity → Nat)
    (copy : Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map
          (family.addressedPrecedingStage automaton))
        (NatPresburger.extendValuation parameters copy)
        state =
      automaton.runFrom state
        (indices.flatMap fun earlier =>
          Word.power (family.pump earlier)
              (parameters earlier) ++
            family.separator earlier) := by
  induction indices generalizing state with
  | nil => rfl
  | cons earlier indices ih =>
      simp only [List.map_cons,
        PoweredStateStage.evaluate,
        addressedPrecedingStage,
        NatPresburger.extendValuation_castSucc,
        List.flatMap_cons]
      rw [ih]
      rw [automaton.runFrom_append,
        automaton.runFrom_append,
        automaton.runFrom_word_power_eq_iterate]

theorem evaluate_addressedDFAStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    PoweredStateStage.evaluate
        (family.addressedDFAStages automaton index offset)
        (NatPresburger.extendValuation parameters copy)
        (automaton.run family.initial) =
      DFA.stateAfterAddress automaton family parameters
        index copy offset := by
  unfold addressedDFAStages
  rw [PoweredStateStage.evaluate_append]
  rw [family.evaluate_addressedPrecedingStages]
  simp only [PoweredStateStage.evaluate,
    addressedFinalStage,
    NatPresburger.extendValuation_last]
  unfold DFA.stateAfterAddress precedingWord
  rw [automaton.runFrom_word_power_eq_iterate]

noncomputable def addressedStateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (target : Q) :
    NatPresburger (arity + 1) :=
  NatPresburger.poweredStateFormula
    (family.addressedDFAStages automaton index offset)
    (automaton.run family.initial) target

theorem eval_addressedStateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (target : Q) :
    (family.addressedStateFormula automaton index offset
        target).Eval
          (NatPresburger.extendValuation parameters copy) ↔
      DFA.stateAfterAddress automaton family parameters
        index copy offset = target := by
  rw [addressedStateFormula,
    NatPresburger.poweredStateFormula_correct,
    family.evaluate_addressedDFAStages]

noncomputable def addressedStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger (arity + 1) :=
  by
    classical
    exact NatPresburger.disjoin <|
      (Finset.univ.toList.filter
        (fun state => decide (predicate state))).map fun state =>
          family.addressedStateFormula automaton index
            offset state

theorem eval_addressedStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (predicate : Q → Prop) :
    (family.addressedStatePredicateFormula automaton index
        offset predicate).Eval
          (NatPresburger.extendValuation parameters copy) ↔
      predicate
        (DFA.stateAfterAddress automaton family parameters
          index copy offset) := by
  classical
  rw [addressedStatePredicateFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, List.mem_filter,
      Finset.mem_toList, Finset.mem_univ, true_and] at hformula
    obtain ⟨state, hpredicate, rfl⟩ := hformula
    have hpredicate' : predicate state :=
      of_decide_eq_true hpredicate
    have hstate :=
      (family.eval_addressedStateFormula_iff
        automaton parameters index copy offset state).1 heval
    rw [hstate]
    exact hpredicate'
  · intro hpredicate
    let state :=
      DFA.stateAfterAddress automaton family parameters
        index copy offset
    refine ⟨family.addressedStateFormula automaton index
        offset state, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨state, ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨by simp, decide_eq_true hpredicate⟩
    · exact
        (family.eval_addressedStateFormula_iff
          automaton parameters index copy offset state).2 rfl

noncomputable def addressedAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    NatPresburger (arity + 1) :=
  family.addressedStatePredicateFormula automaton index
    offset automaton.accept

theorem eval_addressedAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    (family.addressedAcceptanceFormula automaton index
        offset).Eval
          (NatPresburger.extendValuation parameters copy) ↔
      automaton.Accepts
        (family.addressPrefix parameters index copy offset) := by
  rw [addressedAcceptanceFormula,
    family.eval_addressedStatePredicateFormula_iff]
  unfold DFA.Accepts
  rw [DFA.run_addressPrefix]

end LinearWordFamily

end NSSE
