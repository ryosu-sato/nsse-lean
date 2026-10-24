import NSSE.FiniteReachabilityGame
import NSSE.NumberedTaggedCompiler

/-!
# Unary numbered rule systems as finite reachability games

Enumerated compiler states become game vertices.  A decoded enabled unary
transition becomes a game edge, and the numbered terminal bit seeds the
reachability attractor.
-/

namespace NSSE

universe u

def NumberedRuleSystem.unaryGame
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool) :
    FiniteReachabilityGame where
  stateCount := system.states.stateCount
  accepting := system.numberedTerminal
  witnessTurn := fun index =>
    match system.states.decode index with
    | some state => witnessTurn state
    | none => false
  edge := fun parentIndex childIndex =>
    match system.states.decode parentIndex,
        system.states.decode childIndex with
    | some parent, some child =>
        system.enabled parent [child]
    | _, _ => false

theorem NumberedRuleSystem.unaryGame_accepting_eq
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool)
    {index : Nat} {state : State}
    (hdecode : system.states.decode index = some state) :
    (system.unaryGame witnessTurn).accepting index =
      system.terminal state := by
  exact system.numberedTerminal_eq hdecode

theorem NumberedRuleSystem.unaryGame_turn_eq
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool)
    {index : Nat} {state : State}
    (hdecode : system.states.decode index = some state) :
    (system.unaryGame witnessTurn).witnessTurn index =
      witnessTurn state := by
  simp [NumberedRuleSystem.unaryGame, hdecode]

theorem NumberedRuleSystem.unaryGame_edge_eq
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool)
    {parentIndex childIndex : Nat}
    {parent child : State}
    (hparent :
      system.states.decode parentIndex = some parent)
    (hchild :
      system.states.decode childIndex = some child) :
    (system.unaryGame witnessTurn).edge
        parentIndex childIndex =
      system.enabled parent [child] := by
  simp [NumberedRuleSystem.unaryGame, hparent, hchild]

theorem NumberedRuleSystem.unaryGame_decide_correct
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool)
    (index : Nat) (hindex : index < system.states.stateCount) :
    (system.unaryGame witnessTurn).decideWinning index = true ↔
      (system.unaryGame witnessTurn).Winning index := by
  exact FiniteReachabilityGame.decideWinning_correct
    (system.unaryGame witnessTurn) index hindex

theorem NumberedRuleSystem.unaryGameWinning_sound
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool)
    (meaning : State → Prop)
    (terminalSound :
      ∀ state,
        system.terminal state = true →
        meaning state)
    (witnessSound :
      ∀ parent child,
        witnessTurn parent = true →
        system.enabled parent [child] = true →
        meaning child →
        meaning parent)
    (opponentSound :
      ∀ parent,
        witnessTurn parent = false →
        (∀ child,
          system.enabled parent [child] = true →
          meaning child) →
        meaning parent)
    {index : Nat}
    (hwinning :
      (system.unaryGame witnessTurn).Winning index) :
    ∃ state,
      system.states.decode index = some state ∧
      meaning state := by
  let indexMeaning := fun index =>
    ∃ state,
      system.states.decode index = some state ∧
      meaning state
  apply hwinning.sound (meaning := indexMeaning)
  · intro stateIndex hstate haccepting
    obtain ⟨state, hdecode⟩ :=
      system.states.decode_of_lt hstate
    exact ⟨state, hdecode,
      terminalSound state (by
        rw [← system.unaryGame_accepting_eq witnessTurn hdecode]
        exact haccepting)⟩
  · intro parentIndex childIndex hparent hturn hchild hmeaning
    obtain ⟨parent, hparentDecode⟩ :=
      system.states.decode_of_lt hparent
    have hchildBound :=
      (system.unaryGame witnessTurn).successor_lt hchild
    obtain ⟨child, hchildDecode⟩ :=
      system.states.decode_of_lt hchildBound
    obtain ⟨meaningChild, hmeaningDecode, hmeaningChild⟩ := hmeaning
    rw [hchildDecode] at hmeaningDecode
    simp only [Option.some.injEq] at hmeaningDecode
    subst meaningChild
    exact ⟨parent, hparentDecode,
      witnessSound parent child
        (by
          rw [← system.unaryGame_turn_eq
            witnessTurn hparentDecode]
          exact hturn)
        (by
          rw [← system.unaryGame_edge_eq
            witnessTurn hparentDecode hchildDecode]
          exact (List.mem_filter.mp hchild).2)
        hmeaningChild⟩
  · intro parentIndex hparent hturn hall
    obtain ⟨parent, hparentDecode⟩ :=
      system.states.decode_of_lt hparent
    refine ⟨parent, hparentDecode,
      opponentSound parent (by
        rw [← system.unaryGame_turn_eq
          witnessTurn hparentDecode]
        exact hturn) ?_⟩
    intro child henabled
    obtain ⟨childIndex, hchildBound, hchildDecode⟩ :=
      system.states.exists_index_decode child
    have hedge :
        (system.unaryGame witnessTurn).edge
          parentIndex childIndex = true := by
      rw [system.unaryGame_edge_eq
        witnessTurn hparentDecode hchildDecode]
      exact henabled
    have hsuccessor :
        childIndex ∈
          (system.unaryGame witnessTurn).successors parentIndex :=
      (system.unaryGame witnessTurn).successor_mem
        hchildBound hedge
    obtain ⟨decoded, hdecoded, hmeaning⟩ :=
      hall childIndex hsuccessor
    rw [hchildDecode] at hdecoded
    simp only [Option.some.injEq] at hdecoded
    subst decoded
    exact hmeaning

theorem NumberedRuleSystem.unaryGameDecision_sound
    (system : NumberedRuleSystem State)
    (witnessTurn : State → Bool)
    (meaning : State → Prop)
    (terminalSound :
      ∀ state,
        system.terminal state = true →
        meaning state)
    (witnessSound :
      ∀ parent child,
        witnessTurn parent = true →
        system.enabled parent [child] = true →
        meaning child →
        meaning parent)
    (opponentSound :
      ∀ parent,
        witnessTurn parent = false →
        (∀ child,
          system.enabled parent [child] = true →
          meaning child) →
        meaning parent)
    (index : Nat)
    (hindex : index < system.states.stateCount)
    (haccept :
      (system.unaryGame witnessTurn).decideWinning index = true) :
    ∃ state,
      system.states.decode index = some state ∧
      meaning state := by
  apply system.unaryGameWinning_sound
    witnessTurn meaning terminalSound witnessSound opponentSound
  exact ((system.unaryGame_decide_correct
    witnessTurn index hindex).1 haccept)

theorem NumberedRuleSystem.allWitnessUnaryGameWinning_sound
    (system : NumberedRuleSystem State)
    (meaning : State → Prop)
    (terminalSound :
      ∀ state,
        system.terminal state = true →
        meaning state)
    (moveSound :
      ∀ parent child,
        system.enabled parent [child] = true →
        meaning child →
        meaning parent)
    {index : Nat}
    (hwinning :
      (system.unaryGame (fun _ => true)).Winning index) :
    ∃ state,
      system.states.decode index = some state ∧
      meaning state := by
  apply system.unaryGameWinning_sound
    (fun _ => true) meaning terminalSound
  · intro parent child _ henabled hchild
    exact moveSound parent child henabled hchild
  · intro parent hfalse _
    simp at hfalse
  · exact hwinning

theorem NumberedRuleSystem.allWitnessUnaryGameDecision_sound
    (system : NumberedRuleSystem State)
    (meaning : State → Prop)
    (terminalSound :
      ∀ state,
        system.terminal state = true →
        meaning state)
    (moveSound :
      ∀ parent child,
        system.enabled parent [child] = true →
        meaning child →
        meaning parent)
    (index : Nat)
    (hindex : index < system.states.stateCount)
    (haccept :
      (system.unaryGame
        (fun _ => true)).decideWinning index = true) :
    ∃ state,
      system.states.decode index = some state ∧
      meaning state := by
  apply system.allWitnessUnaryGameWinning_sound
    meaning terminalSound moveSound
  exact ((system.unaryGame_decide_correct
    (fun _ => true) index hindex).1 haccept)

end NSSE
