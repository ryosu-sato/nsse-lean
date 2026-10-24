import NSSE.FullyComposedUnaryMoveClassification
import NSSE.GeneralizedStateMaskProgress

/-!
# Same-rank moves of the mask-refined fully composed compiler

An enabled unary refined move of unchanged mask rank leaves both masks
unchanged.  Its underlying compiler transition is therefore classified
entirely by the fully composed base system.
-/

namespace NSSE

universe u

def compilerIntervalSpan
    (tag : IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass) : Nat :=
  match tag.interval? with
  | some interval => interval.span
  | none => 0

def fullyComposedProgressMeasure
    (atomCount queryCount : Nat)
    (state :
      GeneralizedState
        (IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass)) :
    Nat × Nat :=
  (remainingMaskCapacity atomCount queryCount state,
    compilerIntervalSpan state.tag)

def NatPairLexLt (child parent : Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (· < ·) child parent

theorem natPairLexLt_wellFounded :
    WellFounded NatPairLexLt := by
  exact (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

theorem progressMeasure_lt_of_capacity_lt
    {atomCount queryCount : Nat}
    {parent child :
      GeneralizedState
        (IntervalCompilerTag Ctl Cut Ori Macro Wire Atom QClass)}
    (hcapacity :
      remainingMaskCapacity atomCount queryCount child <
        remainingMaskCapacity atomCount queryCount parent) :
    NatPairLexLt
      (fullyComposedProgressMeasure atomCount queryCount child)
      (fullyComposedProgressMeasure atomCount queryCount parent) := by
  apply Prod.lex_def.mpr
  exact Or.inl hcapacity

theorem FullyComposedStrictMove.intervalSpan_lt
    {attachment : AttachmentDomains}
    {parent child :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        Atom QClass}
    (hstrict : FullyComposedStrictMove attachment parent child) :
    compilerIntervalSpan child < compilerIntervalSpan parent := by
  obtain ⟨control, cutValue, parentInterval, childInterval,
      rfl, hchild, _hdelegate, hspan⟩ := hstrict
  change
    (match child.interval? with
      | some interval => interval.span
      | none => 0) < parentInterval.span
  rw [hchild]
  exact hspan

theorem progressMeasure_lt_of_strictMove
    {atomCount queryCount : Nat}
    {attachment : AttachmentDomains}
    {parent child :
      GeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass)}
    (hmasks :
      parent.guarded = child.guarded ∧
        parent.forbidden = child.forbidden)
    (hstrict :
      FullyComposedStrictMove attachment parent.tag child.tag) :
    NatPairLexLt
      (fullyComposedProgressMeasure atomCount queryCount child)
      (fullyComposedProgressMeasure atomCount queryCount parent) := by
  apply Prod.lex_def.mpr
  right
  constructor
  · unfold fullyComposedProgressMeasure remainingMaskCapacity
      generalizedMaskRank
    simp only [hmasks.1, hmasks.2]
  · exact hstrict.intervalSpan_lt

theorem generalizedState_eq_of_identityMove
    {summaryOf : LoopId → LoopSummary Wire}
    {parent child :
      GeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass)}
    (hmasks :
      parent.guarded = child.guarded ∧
        parent.forbidden = child.forbidden)
    (hidentity :
      FullyComposedIdentityMove summaryOf parent.tag child.tag) :
    parent = child := by
  cases parent with
  | mk parentTag parentGuarded parentForbidden =>
      cases child with
      | mk childTag childGuarded childForbidden =>
          simp only [GeneralizedState.tag, GeneralizedState.guarded,
            GeneralizedState.forbidden] at hmasks hidentity
          rcases hmasks with ⟨rfl, rfl⟩
          rcases hidentity with ⟨rfl, _⟩
          rfl

theorem fullyComposed_sameRank_unary_enabled_cases
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (atomCount queryCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)
        atomCount queryCount)
    (henabled :
      (requiredLabelledGeneralizedStateRuleSystem
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount queryCount requirement labels).enabled
          parent [child] = true)
    (hrank :
      generalizedMaskRank parent.1 =
        generalizedMaskRank child.1) :
    (parent.1.guarded = child.1.guarded ∧
      parent.1.forbidden = child.1.forbidden) ∧
    (FullyComposedIdentityMove summaryOf parent.1.tag child.1.tag ∨
      FullyComposedStrictMove attachment parent.1.tag child.1.tag ∨
      FullyComposedLocalMove localEnabled parent.1.tag child.1.tag) := by
  have hparts :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient).enabled
          parent.1.tag [child.1.tag] = true ∧
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent.1 [child.1] = true := by
    simpa [requiredLabelledGeneralizedStateRuleSystem,
      labelledGeneralizedStateRuleSystem,
      transitionGeneralizedStateRuleSystem] using henabled
  constructor
  · exact labelled_masks_eq_of_follow_and_rank_eq
      labels parent.1 child.1 hparts.2 hrank
  · apply fullyComposed_unary_enabled_cases
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal parent.1.tag child.1.tag
    simpa [fullyComposedRuleSystem,
      CompilerTagRuleTests.ruleSystem] using hparts.1

theorem fullyComposed_unary_enabled_progress_cases
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    [DecidableEq LocalId] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass →
        Bool)
    (localTerminal : LocalId → Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId) (locals : Enumeration LocalId)
    (quotient : Enumeration QClass)
    (atomCount queryCount : Nat)
    (requirement :
      TerminalMaskRequirement
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (labels :
      TransitionMaskLabels
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass))
    (parent child :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
          QClass)
        atomCount queryCount)
    (henabled :
      (requiredLabelledGeneralizedStateRuleSystem
        (fullyComposedRuleSystem summaryOf attachment
          I left right rightFinal event w j t
          localEnabled localTerminal
          ctl cut ori intervals macros wires loops locals quotient)
        atomCount queryCount requirement labels).enabled
          parent [child] = true) :
    remainingMaskCapacity atomCount queryCount child.1 <
        remainingMaskCapacity atomCount queryCount parent.1 ∨
      ((parent.1.guarded = child.1.guarded ∧
          parent.1.forbidden = child.1.forbidden) ∧
        (FullyComposedIdentityMove summaryOf parent.1.tag child.1.tag ∨
          FullyComposedStrictMove attachment parent.1.tag child.1.tag ∨
          FullyComposedLocalMove localEnabled
            parent.1.tag child.1.tag)) := by
  have hparts :
      (fullyComposedRuleSystem summaryOf attachment
        I left right rightFinal event w j t
        localEnabled localTerminal
        ctl cut ori intervals macros wires loops locals quotient).enabled
          parent.1.tag [child.1.tag] = true ∧
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent.1 [child.1] = true := by
    simpa [requiredLabelledGeneralizedStateRuleSystem,
      labelledGeneralizedStateRuleSystem,
      transitionGeneralizedStateRuleSystem] using henabled
  have hguarded :
      MaskLe parent.1.guarded child.1.guarded := by
    rw [allStateMasksFollow_correct] at hparts
    rw [(hparts.2 child.1 (by simp)).1]
    exact maskLe_markMany _ _
  have hforbidden :
      MaskLe parent.1.forbidden child.1.forbidden := by
    rw [allStateMasksFollow_correct] at hparts
    rw [(hparts.2 child.1 (by simp)).2]
    exact maskLe_markMany _ _
  by_cases hrank :
      generalizedMaskRank parent.1 = generalizedMaskRank child.1
  · right
    exact fullyComposed_sameRank_unary_enabled_cases
      summaryOf attachment I left right rightFinal event w j t
      localEnabled localTerminal
      ctl cut ori intervals macros wires loops locals quotient
      atomCount queryCount requirement labels parent child henabled hrank
  · left
    have hmono :=
      generalizedMaskRank_mono hguarded hforbidden
    have hparentBound :=
      generalizedMaskRank_le parent.2
    have hchildBound :=
      generalizedMaskRank_le child.2
    unfold remainingMaskCapacity
    omega

theorem fullyComposed_measure_or_residual_cases
    {atomCount queryCount : Nat}
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass →
        Bool}
    {parent child :
      GeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass)}
    (hcases :
      remainingMaskCapacity atomCount queryCount child <
          remainingMaskCapacity atomCount queryCount parent ∨
        ((parent.guarded = child.guarded ∧
            parent.forbidden = child.forbidden) ∧
          (FullyComposedIdentityMove summaryOf parent.tag child.tag ∨
            FullyComposedStrictMove attachment parent.tag child.tag ∨
            FullyComposedLocalMove localEnabled parent.tag child.tag))) :
    NatPairLexLt
        (fullyComposedProgressMeasure atomCount queryCount child)
        (fullyComposedProgressMeasure atomCount queryCount parent) ∨
      ((parent.guarded = child.guarded ∧
          parent.forbidden = child.forbidden) ∧
        (FullyComposedIdentityMove summaryOf parent.tag child.tag ∨
          FullyComposedLocalMove localEnabled parent.tag child.tag)) := by
  rcases hcases with hcapacity | ⟨hmasks, hmove⟩
  · exact Or.inl (progressMeasure_lt_of_capacity_lt hcapacity)
  · rcases hmove with hidentity | hstrict | hlocal
    · exact Or.inr ⟨hmasks, Or.inl hidentity⟩
    · exact Or.inl
        (progressMeasure_lt_of_strictMove hmasks hstrict)
    · exact Or.inr ⟨hmasks, Or.inr hlocal⟩

theorem fullyComposed_measure_or_self_or_local
    {atomCount queryCount : Nat}
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass →
        Bool}
    {parent child :
      GeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          Atom QClass)}
    (hcases :
      remainingMaskCapacity atomCount queryCount child <
          remainingMaskCapacity atomCount queryCount parent ∨
        ((parent.guarded = child.guarded ∧
            parent.forbidden = child.forbidden) ∧
          (FullyComposedIdentityMove summaryOf parent.tag child.tag ∨
            FullyComposedStrictMove attachment parent.tag child.tag ∨
            FullyComposedLocalMove localEnabled parent.tag child.tag))) :
    NatPairLexLt
        (fullyComposedProgressMeasure atomCount queryCount child)
        (fullyComposedProgressMeasure atomCount queryCount parent) ∨
      parent = child ∨
      FullyComposedLocalMove localEnabled parent.tag child.tag := by
  rcases fullyComposed_measure_or_residual_cases hcases with
      hmeasure | ⟨hmasks, hidentity | hlocal⟩
  · exact Or.inl hmeasure
  · exact Or.inr (Or.inl
      (generalizedState_eq_of_identityMove hmasks hidentity))
  · exact Or.inr (Or.inr hlocal)

end NSSE
