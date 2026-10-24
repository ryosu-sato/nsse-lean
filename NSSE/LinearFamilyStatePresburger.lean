import NSSE.LinearFamilyAddress
import NSSE.PoweredStatePresburger

/-!
# DFA states on a linear word family are Presburger

This instantiates the generic powered-state compiler with the pumped words
and separators of a linear family.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

def dfaStage
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    PoweredStateStage arity Q where
  coordinate := index
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state (family.separator index)

def dfaStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity) :
    List (PoweredStateStage arity Q) :=
  (List.finRange arity).map
    (family.dfaStage automaton)

theorem evaluate_dfaStages_aux
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (indices : List (Fin arity))
    (parameters : Fin arity → Nat)
    (state : Q) :
    PoweredStateStage.evaluate
        (indices.map (family.dfaStage automaton))
        parameters state =
      automaton.runFrom state
        (indices.flatMap fun index =>
          Word.power (family.pump index)
              (parameters index) ++
            family.separator index) := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons,
        PoweredStateStage.evaluate,
        dfaStage, List.flatMap_cons]
      rw [ih]
      rw [automaton.runFrom_append,
        automaton.runFrom_append,
        automaton.runFrom_word_power_eq_iterate]

theorem evaluate_dfaStages
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    PoweredStateStage.evaluate
        (family.dfaStages automaton)
        parameters (automaton.run family.initial) =
      automaton.run (family.word parameters) := by
  rw [dfaStages, evaluate_dfaStages_aux]
  unfold word
  exact (automaton.run_append _ _).symm

/-- The full Lemma A.0 state condition for a linear family: equality of
the final DFA state to a fixed target is represented by a multivariable
Presburger formula. -/
theorem dfaState_presburger
    (automaton : DFA α Q) [Fintype Q]
    (family : LinearWordFamily α arity)
    (target : Q) :
    ∃ formula : NatPresburger arity,
      ∀ parameters,
        formula.Eval parameters ↔
          automaton.run (family.word parameters) =
            target := by
  let formula :=
    NatPresburger.poweredStateFormula
      (family.dfaStages automaton)
      (automaton.run family.initial) target
  refine ⟨formula, ?_⟩
  intro parameters
  rw [show formula =
      NatPresburger.poweredStateFormula
        (family.dfaStages automaton)
        (automaton.run family.initial) target by rfl]
  rw [NatPresburger.poweredStateFormula_correct,
    family.evaluate_dfaStages]

/-- Acceptance of every member of a linear family is Presburger. -/
theorem dfaAcceptance_presburger
    (automaton : DFA α Q) [Fintype Q]
    (family : LinearWordFamily α arity) :
    ∃ formula : NatPresburger arity,
      ∀ parameters,
        formula.Eval parameters ↔
          automaton.Accepts
            (family.word parameters) := by
  classical
  let acceptingStates : List Q :=
    Finset.univ.toList.filter
      (fun state => decide (automaton.accept state))
  let formulas : List (NatPresburger arity) :=
    acceptingStates.map fun state =>
      Classical.choose
        (family.dfaState_presburger automaton state)
  refine ⟨NatPresburger.disjoin formulas, ?_⟩
  intro parameters
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [formulas, List.mem_map] at hformula
    obtain ⟨state, hstate, rfl⟩ := hformula
    have hrun :=
      (Classical.choose_spec
        (family.dfaState_presburger automaton state)
        parameters).1 heval
    unfold DFA.Accepts
    rw [hrun]
    simp only [acceptingStates, List.mem_filter,
      Finset.mem_toList, Finset.mem_univ, true_and] at hstate
    exact of_decide_eq_true hstate
  · intro haccept
    let state := automaton.run (family.word parameters)
    refine ⟨Classical.choose
        (family.dfaState_presburger automaton state),
      ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨state, ?_, rfl⟩
      simp only [acceptingStates, List.mem_filter,
        Finset.mem_toList, Finset.mem_univ, true_and]
      exact decide_eq_true haccept
    · exact
        (Classical.choose_spec
          (family.dfaState_presburger automaton state)
          parameters).2 rfl

end LinearWordFamily

end NSSE
