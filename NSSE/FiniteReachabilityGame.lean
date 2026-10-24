import NSSE.HornCompiler

/-!
# Executable finite reachability game

Witness-owned states enter the attractor when some successor is already
winning.  Opponent-owned states enter when every finite successor is
winning.  Accepting states seed the least attractor.
-/

namespace NSSE

structure FiniteReachabilityGame where
  stateCount : Nat
  accepting : Nat → Bool
  witnessTurn : Nat → Bool
  edge : Nat → Nat → Bool

namespace FiniteReachabilityGame

def successors (game : FiniteReachabilityGame)
    (state : Nat) : List Nat :=
  (List.range game.stateCount).filter fun child =>
    game.edge state child

def rulesFor (game : FiniteReachabilityGame)
    (state : Nat) : List HornRule :=
  if game.witnessTurn state then
    (game.successors state).map fun child =>
      ⟨state, [child]⟩
  else
    [⟨state, game.successors state⟩]

def rules (game : FiniteReachabilityGame) : List HornRule :=
  (List.range game.stateCount).flatMap game.rulesFor

def compiler (game : FiniteReachabilityGame) :
    FiniteHornCompiler where
  stateCount := game.stateCount
  terminal := game.accepting
  rules := game.rules

def Winning (game : FiniteReachabilityGame) (state : Nat) : Prop :=
  HornDerives game.compiler state

def decideWinning
    (game : FiniteReachabilityGame) (state : Nat) : Bool :=
  decideHornState game.compiler state

theorem decideWinning_correct
    (game : FiniteReachabilityGame)
    (state : Nat) (hstate : state < game.stateCount) :
    game.decideWinning state = true ↔
      game.Winning state := by
  exact decideHornState_correct game.compiler state hstate

theorem accepting_winning
    (game : FiniteReachabilityGame)
    (state : Nat) (hstate : state < game.stateCount)
    (haccepting : game.accepting state = true) :
    game.Winning state := by
  exact .terminal hstate haccepting

theorem successor_mem
    (game : FiniteReachabilityGame)
    {state child : Nat}
    (hchild : child < game.stateCount)
    (hedge : game.edge state child = true) :
    child ∈ game.successors state := by
  simp [successors, hchild, hedge]

theorem successor_lt
    (game : FiniteReachabilityGame)
    {state child : Nat}
    (hchild : child ∈ game.successors state) :
    child < game.stateCount := by
  exact List.mem_range.mp (List.mem_filter.mp hchild).1

theorem witness_rule_mem
    (game : FiniteReachabilityGame)
    {state child : Nat}
    (hstate : state < game.stateCount)
    (hturn : game.witnessTurn state = true)
    (hchild : child ∈ game.successors state) :
    (⟨state, [child]⟩ : HornRule) ∈ game.rules := by
  simp only [rules, List.mem_flatMap]
  refine ⟨state, List.mem_range.mpr hstate, ?_⟩
  simp [rulesFor, hturn, hchild]

theorem opponent_rule_mem
    (game : FiniteReachabilityGame)
    {state : Nat}
    (hstate : state < game.stateCount)
    (hturn : game.witnessTurn state = false) :
    (⟨state, game.successors state⟩ : HornRule) ∈ game.rules := by
  simp only [rules, List.mem_flatMap]
  exact ⟨state, List.mem_range.mpr hstate,
    by simp [rulesFor, hturn]⟩

theorem witness_step_winning
    (game : FiniteReachabilityGame)
    (state child : Nat)
    (hstate : state < game.stateCount)
    (hturn : game.witnessTurn state = true)
    (hchild : child ∈ game.successors state)
    (hwinning : game.Winning child) :
    game.Winning state := by
  unfold Winning at hwinning ⊢
  apply HornDerives.rule
    (rule := ⟨state, [child]⟩)
    (game.witness_rule_mem hstate hturn hchild) hstate
  intro found hfound
  simp only [List.mem_singleton] at hfound
  subst found
  exact hwinning

theorem opponent_step_winning
    (game : FiniteReachabilityGame)
    (state : Nat)
    (hstate : state < game.stateCount)
    (hturn : game.witnessTurn state = false)
    (hall :
      ∀ child ∈ game.successors state,
        game.Winning child) :
    game.Winning state := by
  unfold Winning at hall ⊢
  exact HornDerives.rule
    (rule := ⟨state, game.successors state⟩)
    (game.opponent_rule_mem hstate hturn) hstate hall

theorem rule_mem_cases
    (game : FiniteReachabilityGame)
    (rule : HornRule)
    (hmem : rule ∈ game.rules) :
    (∃ state child,
      state < game.stateCount ∧
      game.witnessTurn state = true ∧
      child ∈ game.successors state ∧
      rule = ⟨state, [child]⟩) ∨
    (∃ state,
      state < game.stateCount ∧
      game.witnessTurn state = false ∧
      rule = ⟨state, game.successors state⟩) := by
  simp only [rules, List.mem_flatMap] at hmem
  obtain ⟨state, hstate, hrule⟩ := hmem
  have hstateBound : state < game.stateCount :=
    List.mem_range.mp hstate
  by_cases hturn : game.witnessTurn state = true
  · left
    simp only [rulesFor, if_pos hturn, List.mem_map] at hrule
    obtain ⟨child, hchild, rfl⟩ := hrule
    exact ⟨state, child, hstateBound, hturn, hchild, rfl⟩
  · right
    have hturnFalse : game.witnessTurn state = false := by
      cases h : game.witnessTurn state
      · rfl
      · exact False.elim (hturn h)
    simp [rulesFor, hturnFalse] at hrule
    subst rule
    exact ⟨state, hstateBound, hturnFalse, rfl⟩

theorem Winning.sound
    (game : FiniteReachabilityGame)
    (meaning : Nat → Prop)
    (acceptingSound :
      ∀ state, state < game.stateCount →
        game.accepting state = true →
        meaning state)
    (witnessSound :
      ∀ state child,
        state < game.stateCount →
        game.witnessTurn state = true →
        child ∈ game.successors state →
        meaning child →
        meaning state)
    (opponentSound :
      ∀ state,
        state < game.stateCount →
        game.witnessTurn state = false →
        (∀ child ∈ game.successors state, meaning child) →
        meaning state)
    {state : Nat}
    (hwinning : game.Winning state) :
    meaning state := by
  unfold Winning at hwinning
  induction hwinning with
  | terminal state_lt terminal_true =>
      exact acceptingSound _ state_lt terminal_true
  | @rule rule rule_mem parent_lt children ih =>
      rcases game.rule_mem_cases rule rule_mem with
        ⟨state, child, hstate, hturn, hchild, hrule⟩ |
        ⟨state, hstate, hturn, hrule⟩
      · subst rule
        apply witnessSound state child hstate hturn hchild
        exact ih child (by simp)
      · subst rule
        exact opponentSound state hstate hturn ih

end FiniteReachabilityGame

end NSSE
