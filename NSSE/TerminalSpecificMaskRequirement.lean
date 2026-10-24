import NSSE.NormalizedGuardedEmissionCoverage

/-!
# Terminal-specific mask requirements

Interval-bearing nonidentity terminals can be realized directly and need
no forbidden mask.  Non-interval terminals use the canonical indexed-root
mask and the first-event guarded requirement.
-/

namespace NSSE

universe u

def terminalSpecificMaskRequirement
    [DecidableEq Query]
    (queries : Enumeration Query) (guardIndex : Guard → Nat) :
    TerminalMaskRequirement
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId Guard LocalId) QClass) where
  guarded := fun tag =>
    match tag.interval? with
    | some _ => []
    | none =>
        guardedIndicesOfCompilerTag guardIndex tag
  forbidden := fun tag =>
    match tag.interval? with
    | some _ => []
    | none => allCanonicalQueryIndices queries

def firstEventTerminalSpecificMaskRequirement
    [DecidableEq Query]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query) :
    TerminalMaskRequirement
      (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
        QClass) :=
  terminalSpecificMaskRequirement queries firstEventGuardIndex

theorem requiredMasksTerminal_terminalSpecific_of_interval_some
    [DecidableEq Query]
    (queries : Enumeration Query)
    (guardIndex : Guard → Nat)
    (atomCount : Nat)
    (state :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)
        atomCount queries.values.length)
    {interval : NatInterval}
    (hinterval : state.1.tag.interval? = some interval) :
    requiredMasksTerminal
      (terminalSpecificMaskRequirement queries guardIndex)
      atomCount queries.values.length state = true := by
  simp [requiredMasksTerminal,
    terminalSpecificMaskRequirement, hinterval,
    allIndicesMarked]

theorem requiredMasksTerminal_terminalSpecific_of_interval_none
    [DecidableEq Query]
    (queries : Enumeration Query)
    (guardIndex : Guard → Nat)
    (atomCount : Nat)
    (state :
      ValidGeneralizedState
        (FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId Guard LocalId) QClass)
        atomCount queries.values.length)
    (hinterval : state.1.tag.interval? = none)
    :
    requiredMasksTerminal
        (terminalSpecificMaskRequirement queries guardIndex)
        atomCount queries.values.length state =
      requiredMasksTerminal
        (allCanonicalForbiddenRequirement queries
          (guardedIndicesOfCompilerTag guardIndex))
        atomCount queries.values.length state := by
  simp [requiredMasksTerminal,
    terminalSpecificMaskRequirement,
    allCanonicalForbiddenRequirement,
    hinterval]

end NSSE
