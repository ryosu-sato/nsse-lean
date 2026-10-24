import NSSE.NumberedTaggedCompiler
import NSSE.TaggedRuleDispatcher
import NSSE.GlobalTerminalBridge

/-!
# Numbered Horn compiler for bounded response tags

The specialized response tag type still contains all six
`CompilerTag` constructors.  Only `.bounded` tags can be terminals and
there are no recursive rules.  This module enumerates the full tag type
and connects its existing exact terminal semantics to the numbered
tagged/Horn compiler.
-/

namespace NSSE

universe u vc vl vr

def unitEnumeration : Enumeration Unit where
  values := [()]
  complete := by
    intro value
    cases value
    simp

def boundedResponseTagEnumeration
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    Enumeration (BoundedResponseTag I left right event w j t) :=
  CompilerTag.enumeration
    unitEnumeration unitEnumeration unitEnumeration unitEnumeration
    unitEnumeration unitEnumeration
    (finiteGuardQueryEnumeration I left right event w j t)
    unitEnumeration

def decideBoundedResponseTag
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    BoundedResponseTag I left right event w j t → Bool
  | .bounded _ _ query =>
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query
  | _ => false

theorem decideBoundedResponseTag_correct
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t) :
    decideBoundedResponseTag I left right rightFinal
        event w j t tag = true ↔
      BoundedResponseTerminal I left right rightFinal
        event w j t tag () := by
  cases tag <;> simp [decideBoundedResponseTag,
    BoundedResponseTerminal]

def boundedResponseRuleTests
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    CompilerTagRuleTests Unit Unit Unit Unit Unit Unit
      (FirstEventFiniteGuardQuery I left right event w j t) Unit where
  arities := fun _ => []
  terminal := fun _ tag =>
    decideBoundedResponseTag I left right rightFinal event w j t tag
  enabled := fun _ _ _ => false

def boundedResponseRuleSystem
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    NumberedRuleSystem
      (BoundedResponseTag I left right event w j t) :=
  (boundedResponseRuleTests I left right rightFinal event w j t
    ).ruleSystem
      unitEnumeration unitEnumeration unitEnumeration unitEnumeration
      unitEnumeration unitEnumeration
      (finiteGuardQueryEnumeration I left right event w j t)
      unitEnumeration

theorem boundedResponseTaggedDerives_iff_terminal
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t) :
    (boundedResponseRuleSystem I left right rightFinal
      event w j t).TaggedDerives tag ↔
      BoundedResponseTerminal I left right rightFinal
        event w j t tag () := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal =>
        exact
          (decideBoundedResponseTag_correct
            I left right rightFinal event w j t tag).1 hterminal
    | rule _ enabled _ =>
        simp [boundedResponseRuleSystem, boundedResponseRuleTests,
          CompilerTagRuleTests.ruleSystem,
          CompilerTagRuleTests.dispatchEnabled] at enabled
  · intro hterminal
    apply NumberedRuleSystem.TaggedDerives.terminal
    exact
      (decideBoundedResponseTag_correct
        I left right rightFinal event w j t tag).2 hterminal

theorem boundedResponseTaggedDerives_iff_compilerDerives
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t) :
    (boundedResponseRuleSystem I left right rightFinal
        event w j t).TaggedDerives tag ↔
      CompilerDerives
        (BoundedResponseTerminal I left right rightFinal event w j t)
        (NoBoundedResponseCompose I left right event w j t)
        tag () := by
  rw [boundedResponseTaggedDerives_iff_terminal,
    boundedResponse_derives_iff_terminal]

theorem boundedResponseHornDerives_iff
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t) :
    (∃ index,
      (boundedResponseRuleSystem I left right rightFinal
          event w j t).states.decode index = some tag ∧
      HornDerives
        (boundedResponseRuleSystem I left right rightFinal
          event w j t).compiler index) ↔
      BoundedResponseTerminal I left right rightFinal
        event w j t tag () := by
  rw [← boundedResponseTaggedDerives_iff_terminal]
  exact
    (boundedResponseRuleSystem I left right rightFinal
      event w j t).taggedDerives_iff_numberedHorn tag |>.symm

theorem decideBoundedResponseState_correct
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t)
    (index : Nat)
    (hdecode :
      (boundedResponseRuleSystem I left right rightFinal
        event w j t).states.decode index = some tag) :
    decideHornState
        (boundedResponseRuleSystem I left right rightFinal
          event w j t).compiler index = true ↔
      BoundedResponseTerminal I left right rightFinal
        event w j t tag () := by
  let system :=
    boundedResponseRuleSystem I left right rightFinal event w j t
  have hindex : index < system.states.stateCount :=
    system.states.decode_some_lt hdecode
  rw [system.decideState_correct index hindex]
  constructor
  · rintro ⟨decoded, hdecoded, hderive⟩
    rw [hdecode] at hdecoded
    simp at hdecoded
    subst decoded
    exact
      (boundedResponseTaggedDerives_iff_terminal
        I left right rightFinal event w j t tag).1 hderive
  · intro hterminal
    exact ⟨tag, hdecode,
      (boundedResponseTaggedDerives_iff_terminal
        I left right rightFinal event w j t tag).2 hterminal⟩

end NSSE
