import NSSE.FullyComposedSemanticRealization

/-!
# Normal form of a fully composed semantic response

Every semantic response is a finite unary path of side/local response
edges ending in exactly one terminal fact.  This file extracts that path
and classifies the endpoint without discarding the parent contexts along
the way.
-/

namespace NSSE

universe u

inductive UnaryResponsePath
    (edge : State → State → Prop) : State → State → Prop
  | refl (state) : UnaryResponsePath edge state state
  | step {parent child terminal}
      (head : edge parent child)
      (tail : UnaryResponsePath edge child terminal) :
      UnaryResponsePath edge parent terminal

theorem UnaryResponsePath.map_edge
    {left right : State → State → Prop}
    (hmap : ∀ parent child, left parent child → right parent child)
    {source target : State}
    (path : UnaryResponsePath left source target) :
    UnaryResponsePath right source target := by
  induction path with
  | refl state =>
      exact .refl state
  | step head tail ih =>
      exact .step (hmap _ _ head) ih

def fullyComposedResponseEdge
    (attachment : AttachmentDomains)
    (localEnabled :
      Ctl → Cut → NatInterval →
        CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass →
          Bool)
    (parent child :
      CompilerTag Ctl Cut Ori NatInterval Macro Wire Atom QClass) :
    Prop :=
  ∃ control cut interval,
    parent = .side control cut interval ∧
    (intervalSideEnabled attachment
        control cut interval child = true ∨
      localEnabled control cut interval child = true)

inductive FullyComposedTerminalFact
    [DecidableEq QC] [DecidableEq QL]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (localTerminal : LocalId → Bool) :
    FiniteLoopCompilerTag Ctl Cut Ori LCA Macro Wire LoopId
      (UnifiedAtomicId
        (FirstEventFiniteGuardQuery I left right event w j t) LocalId)
      QClass → Prop
  | nonidentity
      (tag) (loopId)
      (loop_id : tag.loopId? = some loopId)
      (nonidentity : ¬ IdentityLoop (summaryOf loopId)) :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal tag
  | guard
      (control : Ctl) (cut : Cut)
      (query : FirstEventFiniteGuardQuery
        I left right event w j t)
      (solved :
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query = true) :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal
        (.bounded control cut (.inl query))
  | local
      (control : Ctl) (cut : Cut) (localId : LocalId)
      (terminal : localTerminal localId = true) :
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal
        (.bounded control cut (.inr localId))

theorem FullyComposedSemantic.exists_terminal_path
    [DecidableEq QC] [DecidableEq QL]
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool}
    {localTerminal : LocalId → Bool}
    {state :
      FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
        (UnifiedAtomicId
          (FirstEventFiniteGuardQuery I left right event w j t)
          LocalId)
        QClass}
    (semantic :
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal state) :
    ∃ terminal,
      UnaryResponsePath
        (fullyComposedResponseEdge attachment localEnabled)
        state terminal ∧
      FullyComposedTerminalFact summaryOf I left right rightFinal
        event w j t localTerminal terminal := by
  induction semantic with
  | nonidentity tag loopId hloop hnonidentity =>
      exact ⟨tag, .refl tag,
        .nonidentity tag loopId hloop hnonidentity⟩
  | side control cut parent child henabled hchild ih =>
      obtain ⟨terminal, hpath, hterminal⟩ := ih
      exact ⟨terminal,
        .step
          ⟨control, cut, parent, rfl, Or.inl henabled⟩
          hpath,
        hterminal⟩
  | localResponse control cut parent child henabled hchild ih =>
      obtain ⟨terminal, hpath, hterminal⟩ := ih
      exact ⟨terminal,
        .step
          ⟨control, cut, parent, rfl, Or.inr henabled⟩
          hpath,
        hterminal⟩
  | guard control cut query hsolved =>
      exact ⟨.bounded control cut (.inl query),
        .refl _, .guard control cut query hsolved⟩
  | «local» control cut localId hterminal =>
      exact ⟨.bounded control cut (.inr localId),
        .refl _, .local control cut localId hterminal⟩

theorem selectedSide_realize_of_terminal_paths
    [DecidableEq QC] [DecidableEq QL]
    {soa : SOAInstance β}
    {summaryOf : LoopId → LoopSummary Wire}
    {attachment : AttachmentDomains}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {rightFinal : DFAFinalTest right}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {localEnabled :
      Ctl → Cut → NatInterval →
        FiniteLoopCompilerTag Ctl Cut Ori NatInterval Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            LocalId)
          QClass →
        Bool}
    {localTerminal : LocalId → Bool}
    {roots : List (InitialSideRoot Ctl Cut)}
    (realizeTerminalPath :
      ∀ root ∈ roots, ∀ terminal,
        UnaryResponsePath
          (fullyComposedResponseEdge attachment localEnabled)
          (.side root.control root.cut root.parent) terminal →
        FullyComposedTerminalFact summaryOf I left right rightFinal
          event w j t localTerminal terminal →
        ∃ word : Word β, soa.Avoider word) :
    ∀ root ∈ roots,
      FullyComposedSemantic summaryOf attachment I left right
        rightFinal event w j t localEnabled localTerminal
        (.side root.control root.cut root.parent) →
      ∃ word : Word β, soa.Avoider word := by
  intro root hroot semantic
  obtain ⟨terminal, hpath, hterminal⟩ :=
    semantic.exists_terminal_path
  exact realizeTerminalPath root hroot terminal hpath hterminal

end NSSE
