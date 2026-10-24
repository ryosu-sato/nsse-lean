import NSSE.FiniteGuardTransitionLabels
import NSSE.FiniteFunctionEnumeration

/-!
# Canonical forbidden-query labels

Canonical query types are converted to mask positions by their first index
in a complete finite enumeration.  A transition classifier may emit several
types; every emitted index is in range and is marked by the transition.
-/

namespace NSSE

universe u

def enumerationIndex
    [DecidableEq Query] (queries : Enumeration Query)
    (query : Query) : Nat :=
  queries.values.idxOf query

theorem enumerationIndex_lt
    [DecidableEq Query] (queries : Enumeration Query)
    (query : Query) :
    enumerationIndex queries query < queries.values.length := by
  unfold enumerationIndex
  have auxiliary :
      ∀ (values : List Query), query ∈ values →
        values.idxOf query < values.length := by
    intro values hmem
    induction values with
    | nil =>
        simp at hmem
    | cons head tail ih =>
        by_cases heq : query = head
        · subst head
          simp [List.idxOf, List.findIdx_cons]
        · have htail : query ∈ tail := by
            simpa [heq] using hmem
          rw [List.idxOf, List.findIdx_cons]
          have hhead : (head == query) = false := by
            have hne : head ≠ query := fun h => heq h.symm
            simp [hne]
          simpa [hhead] using htail
  exact auxiliary queries.values (queries.complete query)

def canonicalQueryIndices
    [DecidableEq Query] (queries : Enumeration Query)
    (emitted : List Query) : List Nat :=
  emitted.map (enumerationIndex queries)

theorem mem_canonicalQueryIndices
    [DecidableEq Query] (queries : Enumeration Query)
    (emitted : List Query) (index : Nat) :
    index ∈ canonicalQueryIndices queries emitted ↔
      ∃ query ∈ emitted, enumerationIndex queries query = index := by
  simp [canonicalQueryIndices]

theorem canonicalQueryIndex_lt_of_mem
    [DecidableEq Query] (queries : Enumeration Query)
    (emitted : List Query) (index : Nat)
    (hindex : index ∈ canonicalQueryIndices queries emitted) :
    index < queries.values.length := by
  obtain ⟨query, _, rfl⟩ :=
    (mem_canonicalQueryIndices queries emitted index).1 hindex
  exact enumerationIndex_lt queries query

def canonicalForbiddenIndices
    [DecidableEq Query]
    (queries : Enumeration Query)
    (emitted : Tag → Tag → List Query) :
    Tag → Tag → List Nat :=
  fun parent child =>
    canonicalQueryIndices queries (emitted parent child)

def allCanonicalQueryIndices
    [DecidableEq Query] (queries : Enumeration Query) :
    List Nat :=
  canonicalQueryIndices queries queries.values

theorem enumerationIndex_mem_allCanonicalQueryIndices
    [DecidableEq Query] (queries : Enumeration Query)
    (query : Query) :
    enumerationIndex queries query ∈
      allCanonicalQueryIndices queries := by
  apply (mem_canonicalQueryIndices
    queries queries.values (enumerationIndex queries query)).2
  exact ⟨query, queries.complete query, rfl⟩

theorem allCanonicalQueryIndices_bounded
    [DecidableEq Query] (queries : Enumeration Query)
    (index : Nat)
    (hindex : index ∈ allCanonicalQueryIndices queries) :
    index < queries.values.length := by
  exact canonicalQueryIndex_lt_of_mem
    queries queries.values index hindex

def allCanonicalForbiddenRequirement
    [DecidableEq Query]
    (queries : Enumeration Query)
    (guardedRequired : Tag → List Nat) :
    TerminalMaskRequirement Tag where
  guarded := guardedRequired
  forbidden := fun _ => allCanonicalQueryIndices queries

theorem allCanonicalForbiddenRequirement_correct
    [DecidableEq Query]
    (queries : Enumeration Query)
    (guardedRequired : Tag → List Nat)
    (atomCount : Nat)
    (state :
      ValidGeneralizedState Tag atomCount queries.values.length) :
    requiredMasksTerminal
        (allCanonicalForbiddenRequirement queries guardedRequired)
        atomCount queries.values.length state = true ↔
      (∀ index ∈ guardedRequired state.1.tag,
        maskBit state.1.guarded index = true) ∧
      (∀ query : Query,
        maskBit state.1.forbidden
          (enumerationIndex queries query) = true) := by
  rw [requiredMasksTerminal_correct]
  constructor
  · rintro ⟨hguarded, hforbidden⟩
    exact ⟨hguarded, fun query =>
      hforbidden (enumerationIndex queries query)
        (enumerationIndex_mem_allCanonicalQueryIndices queries query)⟩
  · rintro ⟨hguarded, hall⟩
    refine ⟨hguarded, ?_⟩
    intro index hindex
    obtain ⟨query, _, rfl⟩ :=
      (mem_canonicalQueryIndices
        queries queries.values index).1 hindex
    exact hall query

def canonicalFirstEventTransitionMaskLabels
    [DecidableEq Query]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (emitted :
      CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        List Query) :
    TransitionMaskLabels
      (CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass) :=
  firstEventTransitionMaskLabels
    (canonicalForbiddenIndices queries emitted)

def canonicalFirstEventGeneralizedStateRuleSystem
    [DecidableEq Query]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (base :
      NumberedRuleSystem
        (CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass))
    (atomCount : Nat)
    (queries : Enumeration Query)
    (guardedRequired :
      CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        List Nat)
    (emitted :
      CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        List Query) :
    NumberedRuleSystem
      (ValidGeneralizedState
        (CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass)
        atomCount queries.values.length) :=
  requiredLabelledGeneralizedStateRuleSystem
    base atomCount queries.values.length
      (allCanonicalForbiddenRequirement queries guardedRequired)
      (canonicalFirstEventTransitionMaskLabels queries emitted)

theorem canonicalForbiddenUpdate_marks_emitted
    [DecidableEq Query]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (queries : Enumeration Query)
    (emitted :
      CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        List Query)
    (parent child :
      CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass)
    (query : Query)
    (hquery : query ∈ emitted parent child)
    (mask : List Bool)
    (hlength : mask.length = queries.values.length) :
    maskBit
        (labelledForbiddenUpdate
          (canonicalFirstEventTransitionMaskLabels queries emitted)
          parent child mask)
        (enumerationIndex queries query) = true := by
  apply maskBit_markMany_of_mem
  · simp only [canonicalFirstEventTransitionMaskLabels,
      firstEventTransitionMaskLabels,
      compilerTagTransitionMaskLabels,
      canonicalForbiddenIndices, canonicalQueryIndices, List.mem_map]
    exact ⟨query, hquery, rfl⟩
  · rw [hlength]
    exact enumerationIndex_lt queries query

end NSSE
