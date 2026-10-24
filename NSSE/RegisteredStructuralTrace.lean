import NSSE.UnifiedRegisteredStructuralDispatcher

/-!
# Coherent traces of registered structural steps

A structural execution is registered one step at a time.  The dependent
trace below enforces that every next source is exactly the preceding
target.  If the complete execution changes its endpoint, at least one
registered one-step summary is nonidentity; its emitted tag therefore
derives in the unified compiler.
-/

namespace NSSE

universe u

inductive RegisteredStructuralTrace
    (Wire LoopId : Type u)
    (summaryOf : LoopId → LoopSummary Wire)
    (width predicateCount : Nat) :
    NormalizedLoopState Wire width →
    List (StructuralLoopStep Wire width predicateCount) → Type u
  | nil (source : NormalizedLoopState Wire width) :
      RegisteredStructuralTrace Wire LoopId summaryOf
        width predicateCount source []
  | cons
      (registered :
        RegisteredStructuralStep Wire LoopId width predicateCount
          summaryOf)
      (rest :
        RegisteredStructuralTrace Wire LoopId summaryOf width predicateCount
          (StructuralLoopStep.advance
            registered.source registered.step) steps) :
      RegisteredStructuralTrace Wire LoopId summaryOf width predicateCount
        registered.source (registered.step :: steps)

namespace RegisteredStructuralTrace

inductive Contains :
    {source : NormalizedLoopState Wire width} →
    {steps : List (StructuralLoopStep Wire width predicateCount)} →
    RegisteredStructuralTrace Wire LoopId summaryOf width predicateCount
      source steps →
    RegisteredStructuralStep Wire LoopId width predicateCount
      summaryOf → Prop
  | head {registered rest} :
      Contains (.cons registered rest) registered
  | tail {registered rest candidate} :
      Contains rest candidate →
      Contains (.cons registered rest) candidate

theorem endpoint_ne_exists_nonidentity
    (trace :
      RegisteredStructuralTrace Wire LoopId summaryOf width predicateCount
        source steps)
    (hne :
      (StructuralLoopStep.execution source steps).target ≠ source) :
    ∃ registered :
        RegisteredStructuralStep Wire LoopId width predicateCount
          summaryOf,
      trace.Contains registered ∧
      ¬ IdentityLoop (summaryOf registered.loopId) := by
  induction trace with
  | nil source =>
      exact False.elim (hne rfl)
  | @cons steps registered rest ih =>
      by_cases hhead :
          StructuralLoopStep.advance registered.source registered.step ≠
            registered.source
      · refine ⟨registered, .head, ?_⟩
        rw [registered.summary_registered]
        exact
          (LoopExecution.nonidentity_iff_endpoint_ne
            (StructuralLoopStep.oneStepExecution
              registered.source registered.step)).2
            (by simpa using hhead)
      · have hnext :
            StructuralLoopStep.advance registered.source registered.step =
              registered.source :=
          Classical.not_not.mp hhead
        have htail :
            (StructuralLoopStep.execution
              (StructuralLoopStep.advance
                registered.source registered.step) steps).target ≠
              StructuralLoopStep.advance
                registered.source registered.step := by
          intro heq
          apply hne
          change
            (StructuralLoopStep.execution
              (StructuralLoopStep.advance
                registered.source registered.step) steps).target =
              registered.source
          exact heq.trans hnext
        obtain ⟨candidate, hcontains, hnonidentity⟩ := ih htail
        exact ⟨candidate, .tail hcontains, hnonidentity⟩

theorem endpoint_ne_exists_unifiedDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL]
    (trace :
      RegisteredStructuralTrace Wire LoopId summaryOf width predicateCount
        source steps)
    (hne :
      (StructuralLoopStep.execution source steps).target ≠ source)
    (contextOf :
      RegisteredStructuralStep Wire LoopId width predicateCount
          summaryOf →
        StructuralTagContext Ctl Cut NatInterval Macro)
    (attachment : AttachmentDomains)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    ∃ registered :
        RegisteredStructuralStep Wire LoopId width predicateCount
          summaryOf,
      trace.Contains registered ∧
      (unifiedFiniteRuleSystem summaryOf attachment I left right
        rightFinal event w j t ctl cut orientation intervals macros
        wires loops quotient).TaggedDerives
          (registered.emittedTag
            (Atom :=
              FirstEventFiniteGuardQuery I left right event w j t)
            (contextOf registered)) := by
  obtain ⟨registered, hcontains, hnonidentity⟩ :=
    trace.endpoint_ne_exists_nonidentity hne
  exact ⟨registered, hcontains,
    (registered.emittedTag_unifiedDerives_iff_nonidentity
      summaryOf (contextOf registered) attachment I left right
      rightFinal event w j t ctl cut orientation intervals macros wires
      loops quotient).2 hnonidentity⟩

theorem idempotent_child_identity_or_unifiedDerivation
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (trace :
      RegisteredStructuralTrace Wire LoopId summaryOf
        width predicateCount source steps)
    (contextOf :
      RegisteredStructuralStep Wire LoopId width predicateCount
          summaryOf →
        StructuralTagContext Ctl Cut NatInterval Macro)
    (I : AutomataSOAInstance α QC QL QR)
    {before after : List (FactorTree α)}
    {deleted : FactorTree α} {e : QC → QC}
    (he : (transformationMonoid QC).Idempotent e)
    (hall :
      ∀ tree ∈ before ++ deleted :: after,
        FactorTree.control (transformationMonoid QC)
          I.candidate.letterTransform tree = e)
    (hretained : before ++ after ≠ [])
    (hdeleted : deleted.WellFormed)
    (leftContext rightContext : Word α)
    (hminimal :
      I.toSOA.LengthMinimalAvoider
        (leftContext ++ FactorTree.forestYield
          (before ++ deleted :: after) ++ rightContext))
    (attachment : AttachmentDomains)
    (leftDFA : DFA α QL) (rightDFA : DFA α QR)
    (rightFinal : DFAFinalTest rightDFA)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (intervals : Enumeration NatInterval)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (quotient : Enumeration (EuclideanSymbol predicateCount)) :
    (StructuralLoopStep.execution source steps).target = source ∨
      ∃ row,
        row ∈ I.toSOA.rows ∧
        PeriodicWitness row
          (leftContext ++
            FactorTree.forestYield (before ++ after) ++ rightContext) ∧
        ∃ registered :
            RegisteredStructuralStep Wire LoopId width predicateCount
              summaryOf,
          trace.Contains registered ∧
          (unifiedFiniteRuleSystem summaryOf attachment I leftDFA
            rightDFA rightFinal event w j t ctl cut orientation
            intervals macros wires loops quotient).TaggedDerives
              (registered.emittedTag
                (Atom := FirstEventFiniteGuardQuery
                  I leftDFA rightDFA event w j t)
                (contextOf registered)) := by
  rcases
      (StructuralLoopStep.execution source steps
        ).idempotent_child_execution_identity_or_VBRP
          I he hall hretained hdeleted leftContext rightContext hminimal with
    hidentity | ⟨row, hrow, hperiodic, hterminal⟩
  · exact Or.inl hidentity
  · have hne :
        (StructuralLoopStep.execution source steps).target ≠ source :=
      ((StructuralLoopStep.execution source steps
        ).terminal_derives_iff_endpoint_ne).1 hterminal
    obtain ⟨registered, hcontains, hderive⟩ :=
      trace.endpoint_ne_exists_unifiedDerivation hne contextOf attachment
        I leftDFA rightDFA rightFinal event w j t ctl cut orientation
        intervals macros wires loops quotient
    exact Or.inr
      ⟨row, hrow, hperiodic, registered, hcontains, hderive⟩

end RegisteredStructuralTrace

end NSSE
