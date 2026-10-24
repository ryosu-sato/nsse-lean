import NSSE.LabelledGeneralizedStateRules
import NSSE.UnifiedAtomicDispatcher

/-!
# Guard-response labels extracted from compiler tags

Bounded guard terminals already carry their finite guard query in the tag.
This file extracts its mask index directly.  Canonical forbidden-query
labels remain a separate classifier because those query types are not fields
of the present compiler tags.
-/

namespace NSSE

universe u

def guardedIndicesOfCompilerTag
    (guardIndex : Guard → Nat)
    (tag :
      CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId Guard LocalId) QClass) :
    List Nat :=
  match tag with
  | .bounded _ _ (.inl guard) => [guardIndex guard]
  | _ => []

def compilerTagTransitionMaskLabels
    (guardIndex : Guard → Nat)
    (forbiddenIndices :
      CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId Guard LocalId) QClass →
        CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId Guard LocalId) QClass →
        List Nat) :
    TransitionMaskLabels
      (CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId Guard LocalId) QClass) where
  guarded := fun _ child =>
    guardedIndicesOfCompilerTag guardIndex child
  forbidden := forbiddenIndices

@[simp] theorem compilerTagTransitionMaskLabels_guarded_bounded
    (guardIndex : Guard → Nat)
    (forbiddenIndices :
      CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId Guard LocalId) QClass →
        CompilerTag Ctl Cut Ori LCA Macro Wire
          (UnifiedAtomicId Guard LocalId) QClass →
        List Nat)
    (parent :
      CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId Guard LocalId) QClass)
    (control : Ctl) (cut : Cut) (guard : Guard) :
    (compilerTagTransitionMaskLabels guardIndex forbiddenIndices).guarded
        parent (.bounded control cut (.inl guard)) =
      [guardIndex guard] :=
  rfl

def firstEventGuardIndex
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (query :
      FirstEventFiniteGuardQuery I left right event w j t) : Nat :=
  responseClassIndex (finiteGuardResponseClass query)

theorem firstEventGuardIndex_lt
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (query :
      FirstEventFiniteGuardQuery I left right event w j t) :
    firstEventGuardIndex query < responseInitialMask.length := by
  exact responseClassIndex_lt (finiteGuardResponseClass query)

def firstEventTransitionMaskLabels
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (forbiddenIndices :
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
        List Nat) :
    TransitionMaskLabels
      (CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass) :=
  compilerTagTransitionMaskLabels
    firstEventGuardIndex forbiddenIndices

theorem firstEventGuardUpdate_marks_bounded_query
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (forbiddenIndices :
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
        List Nat)
    (parent :
      CompilerTag Ctl Cut Ori LCA Macro Wire
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass)
    (control : Ctl) (cut : Cut)
    (query :
      FirstEventFiniteGuardQuery I left right event w j t)
    (mask : List Bool)
    (hlength : mask.length = responseInitialMask.length) :
    maskBit
        (labelledGuardedUpdate
          (firstEventTransitionMaskLabels forbiddenIndices)
          parent (.bounded control cut (.inl query)) mask)
        (firstEventGuardIndex query) = true := by
  apply maskBit_markMany_of_mem
  · simp [firstEventTransitionMaskLabels,
      compilerTagTransitionMaskLabels,
      guardedIndicesOfCompilerTag]
  · rw [hlength]
    exact firstEventGuardIndex_lt query

end NSSE
