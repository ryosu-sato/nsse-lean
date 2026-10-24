import NSSE.BoundedTaggedHorn
import NSSE.SideTaggedRules

/-!
# Combined bounded-terminal and unary-side tagged compiler

This is the first multi-family numbered tagged system: bounded tags are
exact terminals, while the unique specialized side tag makes one
executable recursive call to any child tag.
-/

namespace NSSE

universe u vc vl vr

def boundedSideRuleTests
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (sideEnabled :
      BoundedResponseTag I left right event w j t → Bool) :
    CompilerTagRuleTests Unit Unit Unit Unit Unit Unit
      (FirstEventFiniteGuardQuery I left right event w j t) Unit :=
  (boundedResponseRuleTests I left right rightFinal event w j t).merge
    (sideOnlyRuleTests fun _ _ _ child => sideEnabled child)

def boundedSideRuleSystem
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (sideEnabled :
      BoundedResponseTag I left right event w j t → Bool) :
    NumberedRuleSystem
      (BoundedResponseTag I left right event w j t) :=
  (boundedSideRuleTests I left right rightFinal
    event w j t sideEnabled).ruleSystem
      unitEnumeration unitEnumeration unitEnumeration unitEnumeration
      unitEnumeration unitEnumeration
      (finiteGuardQueryEnumeration I left right event w j t)
      unitEnumeration

theorem boundedSide_dispatchTerminal_correct
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (sideEnabled :
      BoundedResponseTag I left right event w j t → Bool)
    (tag : BoundedResponseTag I left right event w j t) :
    (boundedSideRuleTests I left right rightFinal
      event w j t sideEnabled).dispatchTerminal tag = true ↔
      BoundedResponseTerminal I left right rightFinal
        event w j t tag () := by
  unfold boundedSideRuleTests
  rw [CompilerTagRuleTests.merge_dispatchTerminal_true_iff]
  simp only [CompilerTagRuleTests.dispatchTerminal,
    sideOnlyRuleTests, Bool.false_eq_true, or_false,
    boundedResponseRuleTests]
  exact decideBoundedResponseTag_correct
    I left right rightFinal event w j t tag

theorem boundedSide_side_derives_iff
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (sideEnabled :
      BoundedResponseTag I left right event w j t → Bool) :
    (boundedSideRuleSystem I left right rightFinal
      event w j t sideEnabled).TaggedDerives (.side () () ()) ↔
      ∃ child,
        sideEnabled child = true ∧
        (boundedSideRuleSystem I left right rightFinal
          event w j t sideEnabled).TaggedDerives child := by
  let tests :=
    boundedSideRuleTests I left right rightFinal
      event w j t sideEnabled
  change
    (tests.ruleSystem
      unitEnumeration unitEnumeration unitEnumeration unitEnumeration
      unitEnumeration unitEnumeration
      (finiteGuardQueryEnumeration I left right event w j t)
      unitEnumeration).TaggedDerives (.side () () ()) ↔
      ∃ child,
        sideEnabled child = true ∧
        (tests.ruleSystem
          unitEnumeration unitEnumeration unitEnumeration unitEnumeration
          unitEnumeration unitEnumeration
          (finiteGuardQueryEnumeration I left right event w j t)
          unitEnumeration).TaggedDerives child
  rw [tests.taggedDerives_iff_terminal_or_rule]
  have hterminal :
      tests.dispatchTerminal
          (CompilerTag.side () () ()) ≠ true := by
    intro htrue
    have hbounded :=
      (boundedSide_dispatchTerminal_correct
        I left right rightFinal event w j t sideEnabled
          (.side () () ())).1 htrue
    exact hbounded
  simp [hterminal]
  constructor
  · rintro ⟨children, _, henabled, hchildren⟩
    cases children with
    | nil =>
        simp [tests, boundedSideRuleTests,
          CompilerTagRuleTests.merge, boundedResponseRuleTests,
          sideOnlyRuleTests, CompilerTag.kind] at henabled
    | cons child rest =>
        cases rest with
        | nil =>
            have hchild : sideEnabled child = true := by
              simpa [tests, boundedSideRuleTests,
                CompilerTagRuleTests.merge, boundedResponseRuleTests,
                sideOnlyRuleTests, CompilerTag.kind] using henabled
            exact ⟨child, hchild, hchildren child (by simp)⟩
        | cons next rest =>
            simp [tests, boundedSideRuleTests,
              CompilerTagRuleTests.merge, boundedResponseRuleTests,
              sideOnlyRuleTests, CompilerTag.kind] at henabled
  · rintro ⟨child, henabled, hderive⟩
    refine ⟨[child], ?_, ?_, ?_⟩
    · simp [tests, boundedSideRuleTests,
        CompilerTagRuleTests.merge, boundedResponseRuleTests,
        sideOnlyRuleTests, CompilerTag.kind,
        CompilerTagRuleTests.allArities]
    · simp [tests, boundedSideRuleTests,
        CompilerTagRuleTests.merge, boundedResponseRuleTests,
        sideOnlyRuleTests, CompilerTag.kind, henabled]
    · intro candidate hcandidate
      simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hderive

theorem boundedSide_bounded_derives_iff
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (sideEnabled :
      BoundedResponseTag I left right event w j t → Bool)
    (query : FirstEventFiniteGuardQuery I left right event w j t) :
    (boundedSideRuleSystem I left right rightFinal
      event w j t sideEnabled).TaggedDerives
        (boundedResponseTag query) ↔
      finiteGuardFormula I left right event w j t query := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal =>
        have hbounded :=
          (boundedSide_dispatchTerminal_correct
            I left right rightFinal event w j t sideEnabled
              (boundedResponseTag query)).1 hterminal
        exact
          (boundedResponseTerminal_sound
            I left right rightFinal event w j t
              (boundedResponseTag query)).1 hbounded
    | rule _ henabled _ =>
        simp [boundedSideRuleSystem, boundedSideRuleTests,
          CompilerTagRuleTests.ruleSystem,
          CompilerTagRuleTests.dispatchEnabled,
          CompilerTagRuleTests.merge,
          boundedResponseRuleTests, sideOnlyRuleTests,
          boundedResponseTag, CompilerTag.kind] at henabled
  · intro hformula
    apply NumberedRuleSystem.TaggedDerives.terminal
    apply
      (boundedSide_dispatchTerminal_correct
        I left right rightFinal event w j t sideEnabled
          (boundedResponseTag query)).2
    exact
      (boundedResponseTerminal_sound
        I left right rightFinal event w j t
          (boundedResponseTag query)).2 hformula

def solvedBoundedSideSystem
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    NumberedRuleSystem
      (BoundedResponseTag I left right event w j t) :=
  boundedSideRuleSystem I left right rightFinal event w j t
    (decideBoundedResponseTag I left right rightFinal event w j t)

theorem solvedBoundedSide_root_derives_iff
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    (solvedBoundedSideSystem I left right rightFinal
      event w j t).TaggedDerives (.side () () ()) ↔
      ∃ query,
        finiteGuardFormula I left right event w j t query := by
  unfold solvedBoundedSideSystem
  rw [boundedSide_side_derives_iff]
  constructor
  · rintro ⟨child, haccepted, hderive⟩
    have hterminal :=
      (decideBoundedResponseTag_correct
        I left right rightFinal event w j t child).1 haccepted
    cases child with
    | bounded control cut query =>
        exact ⟨query,
          (boundedResponseTerminal_sound
            I left right rightFinal event w j t
              (.bounded control cut query)).1 hterminal⟩
    | nonstrong control cut lca macroData wire =>
        exact False.elim hterminal
    | strong control cut macroData wire quotient =>
        exact False.elim hterminal
    | hub control cut macroData wire =>
        exact False.elim hterminal
    | copy control cut orientation macroData wire =>
        exact False.elim hterminal
    | side control cut lca =>
        exact False.elim hterminal
  · rintro ⟨query, hformula⟩
    let child := boundedResponseTag query
    refine ⟨child, ?_, ?_⟩
    · exact
        (finiteGuardSolver I left right rightFinal
          event w j t).correct query |>.2 hformula
    · exact
        (boundedSide_bounded_derives_iff
          I left right rightFinal event w j t
          (decideBoundedResponseTag I left right rightFinal
            event w j t) query).2 hformula

theorem decideSolvedBoundedSideRoot_correct
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (index : Nat)
    (hdecode :
      (solvedBoundedSideSystem I left right rightFinal
        event w j t).states.decode index = some (.side () () ())) :
    decideHornState
        (solvedBoundedSideSystem I left right rightFinal
          event w j t).compiler index = true ↔
      ∃ query,
        finiteGuardFormula I left right event w j t query := by
  let system :=
    solvedBoundedSideSystem I left right rightFinal event w j t
  have hindex : index < system.states.stateCount :=
    system.states.decode_some_lt hdecode
  rw [system.decideState_correct index hindex]
  constructor
  · rintro ⟨decoded, hdecoded, hderive⟩
    rw [hdecode] at hdecoded
    simp at hdecoded
    subst decoded
    exact
      (solvedBoundedSide_root_derives_iff
        I left right rightFinal event w j t).1 hderive
  · intro hformula
    exact ⟨.side () () (), hdecode,
      (solvedBoundedSide_root_derives_iff
        I left right rightFinal event w j t).2 hformula⟩

end NSSE
