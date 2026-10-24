import NSSE.HornCompiler

/-!
# Complete enumeration of finite Horn rule schemas

For a fixed finite state count and a finite list of admitted arities,
all bounded parent/children tuples are enumerated.  An executable local
label test can then filter that complete candidate list.
-/

namespace NSSE

def stateVectors (stateCount : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | arity + 1 =>
      (List.range stateCount).flatMap fun head =>
        (stateVectors stateCount arity).map (head :: ·)

theorem mem_stateVectors_iff
    (stateCount arity : Nat) (states : List Nat) :
    states ∈ stateVectors stateCount arity ↔
      states.length = arity ∧
      ∀ state ∈ states, state < stateCount := by
  induction arity generalizing states with
  | zero =>
      cases states <;> simp [stateVectors]
  | succ arity ih =>
      constructor
      · intro hmem
        simp only [stateVectors, List.mem_flatMap,
          List.mem_range, List.mem_map] at hmem
        obtain ⟨head, hhead, tail, htail, rfl⟩ := hmem
        have htail' := (ih tail).1 htail
        exact ⟨by simp [htail'.1], by
          intro state hstate
          simp only [List.mem_cons] at hstate
          rcases hstate with rfl | hstate
          · exact hhead
          · exact htail'.2 state hstate⟩
      · rintro ⟨hlength, hbounded⟩
        cases states with
        | nil => simp at hlength
        | cons head tail =>
            have hhead : head < stateCount :=
              hbounded head (by simp)
            have htailLength : tail.length = arity := by
              simp at hlength
              exact hlength
            have htailBounded :
                ∀ state ∈ tail, state < stateCount := by
              intro state hstate
              exact hbounded state (by simp [hstate])
            simp only [stateVectors, List.mem_flatMap,
              List.mem_range, List.mem_map]
            exact ⟨head, hhead, tail,
              (ih tail).2 ⟨htailLength, htailBounded⟩, rfl⟩

def hornRuleCandidates
    (stateCount : Nat) (arities : List Nat) : List HornRule :=
  (List.range stateCount).flatMap fun parent =>
    arities.flatMap fun arity =>
      (stateVectors stateCount arity).map fun children =>
        ⟨parent, children⟩

def HornRule.WellFormed
    (rule : HornRule) (stateCount : Nat)
    (arities : List Nat) : Prop :=
  rule.parent < stateCount ∧
  rule.children.length ∈ arities ∧
  ∀ child ∈ rule.children, child < stateCount

theorem mem_hornRuleCandidates_iff
    (stateCount : Nat) (arities : List Nat) (rule : HornRule) :
    rule ∈ hornRuleCandidates stateCount arities ↔
      rule.WellFormed stateCount arities := by
  rcases rule with ⟨parent, children⟩
  simp only [hornRuleCandidates, List.mem_flatMap,
    List.mem_range, List.mem_map, HornRule.WellFormed]
  constructor
  · rintro ⟨candidateParent, hparent, arity, harity,
      candidateChildren, hchildren, heq⟩
    cases heq
    have hvector :=
      (mem_stateVectors_iff stateCount arity children).1 hchildren
    exact ⟨hparent, hvector.1 ▸ harity, hvector.2⟩
  · rintro ⟨hparent, harity, hchildren⟩
    exact ⟨parent, hparent, children.length, harity,
      children,
      (mem_stateVectors_iff stateCount children.length children).2
        ⟨rfl, hchildren⟩,
      rfl⟩

def enumerateHornRules
    (stateCount : Nat) (arities : List Nat)
    (enabled : HornRule → Bool) : List HornRule :=
  (hornRuleCandidates stateCount arities).filter enabled

theorem mem_enumerateHornRules_iff
    (stateCount : Nat) (arities : List Nat)
    (enabled : HornRule → Bool) (rule : HornRule) :
    rule ∈ enumerateHornRules stateCount arities enabled ↔
      rule.WellFormed stateCount arities ∧
      enabled rule = true := by
  simp [enumerateHornRules, mem_hornRuleCandidates_iff]

def enumeratedHornCompiler
    (stateCount : Nat) (arities : List Nat)
    (terminal : Nat → Bool) (enabled : HornRule → Bool) :
    FiniteHornCompiler where
  stateCount := stateCount
  terminal := terminal
  rules := enumerateHornRules stateCount arities enabled

theorem enumeratedHornCompiler_rule_mem_iff
    (stateCount : Nat) (arities : List Nat)
    (terminal : Nat → Bool) (enabled : HornRule → Bool)
    (rule : HornRule) :
    rule ∈
        (enumeratedHornCompiler
          stateCount arities terminal enabled).rules ↔
      rule.WellFormed stateCount arities ∧
      enabled rule = true :=
  mem_enumerateHornRules_iff stateCount arities enabled rule

inductive EnumeratedHornDerives
    (stateCount : Nat) (arities : List Nat)
    (terminal : Nat → Bool) (enabled : HornRule → Bool) :
    Nat → Prop where
  | terminal {state : Nat}
      (state_lt : state < stateCount)
      (terminal_true : terminal state = true) :
      EnumeratedHornDerives
        stateCount arities terminal enabled state
  | rule {rule : HornRule}
      (wellFormed : rule.WellFormed stateCount arities)
      (enabled_true : enabled rule = true)
      (children :
        ∀ child ∈ rule.children,
          EnumeratedHornDerives
            stateCount arities terminal enabled child) :
      EnumeratedHornDerives
        stateCount arities terminal enabled rule.parent

theorem enumeratedHornDerives_iff
    (stateCount : Nat) (arities : List Nat)
    (terminal : Nat → Bool) (enabled : HornRule → Bool)
    (state : Nat) :
    HornDerives
        (enumeratedHornCompiler
          stateCount arities terminal enabled) state ↔
      EnumeratedHornDerives
        stateCount arities terminal enabled state := by
  constructor
  · intro hderive
    induction hderive with
    | terminal state_lt terminal_true =>
        exact .terminal state_lt terminal_true
    | @rule rule rule_mem parent_lt children ih =>
        have hrule :=
          (enumeratedHornCompiler_rule_mem_iff
            stateCount arities terminal enabled rule).1 rule_mem
        exact .rule hrule.1 hrule.2
          (fun child hchild => ih child hchild)
  · intro hderive
    induction hderive with
    | terminal state_lt terminal_true =>
        exact .terminal state_lt terminal_true
    | @rule rule wellFormed enabled_true children ih =>
        apply HornDerives.rule
          ((enumeratedHornCompiler_rule_mem_iff
            stateCount arities terminal enabled rule).2
              ⟨wellFormed, enabled_true⟩)
          wellFormed.1
        exact fun child hchild => ih child hchild

theorem decideEnumeratedHornState_correct
    (stateCount : Nat) (arities : List Nat)
    (terminal : Nat → Bool) (enabled : HornRule → Bool)
    (state : Nat) (hstate : state < stateCount) :
    decideHornState
        (enumeratedHornCompiler
          stateCount arities terminal enabled) state = true ↔
      EnumeratedHornDerives
        stateCount arities terminal enabled state := by
  rw [decideHornState_correct
    (enumeratedHornCompiler stateCount arities terminal enabled)
    state hstate]
  exact enumeratedHornDerives_iff
    stateCount arities terminal enabled state

end NSSE
