import NSSE.MultivariablePresburger

/-!
# Presburger formulas for finite powered-state compositions

A stage applies one fixed finite-state function a parameterized number of
times and then one fixed separator function. Intermediate states are
eliminated by finite disjunction.
-/

namespace NSSE

universe v

structure PoweredStateStage (arity : Nat) (Q : Type v) where
  coordinate : Fin arity
  powerStep : Q → Q
  separatorStep : Q → Q

namespace PoweredStateStage

def evaluate :
    List (PoweredStateStage arity Q) →
      (Fin arity → Nat) → Q → Q
  | [], _, state => state
  | stage :: stages, parameters, state =>
      evaluate stages parameters
        (stage.separatorStep
          ((stage.powerStep^[parameters stage.coordinate])
            state))

theorem evaluate_append
    (first second : List (PoweredStateStage arity Q))
    (parameters : Fin arity → Nat)
    (state : Q) :
    evaluate (first ++ second) parameters state =
      evaluate second parameters
        (evaluate first parameters state) := by
  induction first generalizing state with
  | nil => rfl
  | cons stage stages ih =>
      simp only [List.cons_append, evaluate]
      exact ih _

end PoweredStateStage

namespace NatPresburger

def truth : NatPresburger arity :=
  .equal (.const 0) (.const 0)

def disjoin : List (NatPresburger arity) →
    NatPresburger arity
  | [] => .falsum
  | formula :: formulas =>
      .disj formula (disjoin formulas)

theorem eval_disjoin_iff
    (formulas : List (NatPresburger arity))
    (valuation : Fin arity → Nat) :
    (disjoin formulas).Eval valuation ↔
      ∃ formula ∈ formulas, formula.Eval valuation := by
  induction formulas with
  | nil => simp [disjoin, Eval]
  | cons formula formulas ih =>
      simp [disjoin, Eval, ih]

noncomputable def poweredStateFormula
    [Fintype Q]
    (stages : List (PoweredStateStage arity Q))
    (start target : Q) :
    NatPresburger arity := by
  classical
  exact
    match stages with
    | [] =>
        if start = target then truth else .falsum
    | stage :: rest =>
        disjoin <|
          Finset.univ.toList.map fun intermediate =>
            let unary :=
              Classical.choose
                (finite_orbit_eq_presburger
                  stage.powerStep start intermediate)
            .conj
              (embedUnary stage.coordinate unary)
              (poweredStateFormula rest
                (stage.separatorStep intermediate) target)
termination_by stages.length

theorem poweredStateFormula_correct
    [Fintype Q]
    (stages : List (PoweredStateStage arity Q))
    (start target : Q)
    (valuation : Fin arity → Nat) :
    (poweredStateFormula stages start target).Eval valuation ↔
      PoweredStateStage.evaluate stages valuation start =
        target := by
  classical
  induction stages generalizing start with
  | nil =>
      by_cases h : start = target
      · simp [poweredStateFormula, PoweredStateStage.evaluate,
          truth, Eval, h]
      · simp [poweredStateFormula, PoweredStateStage.evaluate,
          truth, Eval, h]
  | cons stage rest ih =>
      rw [poweredStateFormula]
      rw [eval_disjoin_iff]
      constructor
      · rintro ⟨formula, hformula, heval⟩
        simp only [List.mem_map, Finset.mem_toList,
          Finset.mem_univ, true_and] at hformula
        obtain ⟨intermediate, rfl⟩ := hformula
        rcases heval with ⟨horbit, hrest⟩
        have horbit' :
            (stage.powerStep^[
              valuation stage.coordinate]) start =
                intermediate := by
          rw [eval_embedUnary_iff] at horbit
          exact
            (Classical.choose_spec
              (finite_orbit_eq_presburger
                stage.powerStep start intermediate)
              (valuation stage.coordinate)).1 horbit
        simp only [PoweredStateStage.evaluate]
        rw [horbit']
        exact (ih (stage.separatorStep intermediate)).1 hrest
      · intro heval
        let intermediate :=
          (stage.powerStep^[
            valuation stage.coordinate]) start
        refine ⟨.conj
            (embedUnary stage.coordinate
              (Classical.choose
                (finite_orbit_eq_presburger
                  stage.powerStep start intermediate)))
            (poweredStateFormula rest
              (stage.separatorStep intermediate) target),
          ?_, ?_⟩
        · apply List.mem_map.mpr
          refine ⟨intermediate, ?_, rfl⟩
          simp
        · constructor
          · rw [eval_embedUnary_iff]
            exact
              (Classical.choose_spec
                (finite_orbit_eq_presburger
                  stage.powerStep start intermediate)
                (valuation stage.coordinate)).2 rfl
          · apply (ih (stage.separatorStep intermediate)).2
            simpa [PoweredStateStage.evaluate,
              intermediate] using heval

noncomputable def poweredStatePredicateFormula
    [Fintype Q]
    (stages : List (PoweredStateStage arity Q))
    (start : Q)
    (predicate : Q → Prop) :
    NatPresburger arity := by
  classical
  exact disjoin <|
    (Finset.univ.toList.filter
      (fun state => decide (predicate state))).map fun state =>
        poweredStateFormula stages start state

theorem poweredStatePredicateFormula_correct
    [Fintype Q]
    (stages : List (PoweredStateStage arity Q))
    (start : Q)
    (predicate : Q → Prop)
    (valuation : Fin arity → Nat) :
    (poweredStatePredicateFormula stages start predicate).Eval
        valuation ↔
      predicate
        (PoweredStateStage.evaluate stages valuation start) := by
  classical
  rw [poweredStatePredicateFormula, eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, List.mem_filter,
      Finset.mem_toList, Finset.mem_univ, true_and] at hformula
    obtain ⟨state, hpredicate, rfl⟩ := hformula
    have hstate :=
      (poweredStateFormula_correct stages start state valuation).1
        heval
    rw [hstate]
    exact of_decide_eq_true hpredicate
  · intro hpredicate
    let state :=
      PoweredStateStage.evaluate stages valuation start
    refine ⟨poweredStateFormula stages start state, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨state, ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨by simp, decide_eq_true hpredicate⟩
    · exact
        (poweredStateFormula_correct stages start state valuation).2
          rfl

end NatPresburger

end NSSE
