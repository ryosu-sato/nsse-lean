import NSSE.AnnotatedStreamCompiler

/-!
# Bridge from local response outcomes to global compiler strata

Literal occurrence disequalities are genuine PWE terminals.  Finite
DFA/arithmetic guard failures are not mislabeled as global terminals:
they become `CompilerTag.bounded` states.  The bridge preserves the
corresponding executable solver result exactly.
-/

namespace NSSE

universe u vc vl vr

def finiteGuardQueryEnumeration
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    Enumeration
      (FirstEventFiniteGuardQuery I left right event w j t) where
  values := [.candidateLoop, .beforeLeftLoop, .betweenRight, .afterSlot]
  complete := by
    intro query
    cases query <;> simp

abbrev BoundedResponseTag
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :=
  CompilerTag Unit Unit Unit Unit Unit Unit
    (FirstEventFiniteGuardQuery I left right event w j t) Unit

def boundedResponseTag
    (query : FirstEventFiniteGuardQuery I left right event w j t) :
    BoundedResponseTag I left right event w j t :=
  .bounded () () query

def boundedResponseTags
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    List (BoundedResponseTag I left right event w j t) :=
  (finiteGuardQueryEnumeration I left right event w j t).values.map
    boundedResponseTag

theorem boundedResponseTag_mem
    (query : FirstEventFiniteGuardQuery I left right event w j t) :
    boundedResponseTag query ∈
      boundedResponseTags I left right event w j t := by
  simp only [boundedResponseTags, List.mem_map]
  exact ⟨query,
    (finiteGuardQueryEnumeration I left right event w j t).complete query,
    rfl⟩

abbrev EmptyInput (_α : Type u) : Type u :=
  ULift.{u, 0} Empty

def emptyExactSolver (α : Type u) : ExactSolver (EmptyInput α) where
  formula := fun input => nomatch input.down
  decide := fun input => nomatch input.down
  correct := by
    intro input
    exact nomatch input.down

abbrev ResponsePWETerminal (α : Type u) :=
  CompilerTerminal (SuffixDisequalityQuery α)
    (EmptyInput α) (EmptyInput α) (EmptyInput α)

def responsePWETerminal (query : SuffixDisequalityQuery α) :
    ResponsePWETerminal α :=
  .pwe query

def decideResponsePWETerminal [DecidableEq α]
    (terminal : ResponsePWETerminal α) : Bool :=
  decideTerminal (suffixDisequalitySolver (α := α))
    (emptyExactSolver α) (emptyExactSolver α)
    (emptyExactSolver α) terminal

theorem decideResponsePWETerminal_correct [DecidableEq α]
    (terminal : ResponsePWETerminal α) :
    decideResponsePWETerminal terminal ↔
      terminalFormula (suffixDisequalitySolver (α := α))
        (emptyExactSolver α) (emptyExactSolver α)
        (emptyExactSolver α) terminal := by
  exact decideTerminal_correct
    (suffixDisequalitySolver (α := α))
    (emptyExactSolver α) (emptyExactSolver α)
    (emptyExactSolver α) terminal

abbrev FirstEventGlobalDisposition
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :=
  Sum (BoundedResponseTag I left right event w j t)
    (ResponsePWETerminal α)

def globalDisposition :
    FirstEventTerminalQuery I left right event w j t →
      FirstEventGlobalDisposition I left right event w j t
  | .finiteGuard query => .inl (boundedResponseTag query)
  | .pwe query => .inr (responsePWETerminal query)

def GlobalDispositionSolved
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventGlobalDisposition I left right event w j t → Prop
  | .inl (.bounded _ _ query) =>
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true
  | .inl _ => False
  | .inr terminal =>
      decideResponsePWETerminal terminal = true

theorem globalDisposition_preserves_solver
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (query : FirstEventTerminalQuery I left right event w j t) :
    (firstEventTerminalSolver I left right rightFinal
        event w j t).decide query = true ↔
      GlobalDispositionSolved I left right rightFinal event w j t
        (globalDisposition query) := by
  cases query with
  | finiteGuard query => rfl
  | pwe query =>
      rfl

theorem solvedTerminal_has_globalDisposition
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (terminal : SolvedResponseTerminal I left right rightFinal) :
    ∃ disposition,
      GlobalDispositionSolved I left right rightFinal
        terminal.event terminal.word terminal.source terminal.target
        disposition := by
  refine ⟨globalDisposition terminal.query, ?_⟩
  apply (globalDisposition_preserves_solver
    I left right rightFinal terminal.event terminal.word
      terminal.source terminal.target terminal.query).1
  have hformula :=
    (exactSolver_derives_iff_formula
      (firstEventTerminalSolver I left right rightFinal
        terminal.event terminal.word terminal.source terminal.target)
      terminal.query).1 terminal.derives
  exact
    ((firstEventTerminalSolver I left right rightFinal
      terminal.event terminal.word terminal.source terminal.target
      ).correct terminal.query).2 hformula

theorem validStream_nonavoider_or_globalDisposition
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hwitness : SelectedRowWitness I left right w j t) :
    (¬ I.toSOA.Avoider (InsertionEvent.applyStream events w)) ∨
      ∃ (failedEvent : InsertionEvent α) (failedWord : Word α)
          (failedSource failedTarget : Nat),
        ∃ disposition :
            FirstEventGlobalDisposition I left right
              failedEvent failedWord failedSource failedTarget,
          GlobalDispositionSolved I left right rightFinal
            failedEvent failedWord failedSource failedTarget
            disposition := by
  rcases validStream_nonavoider_or_solvedTerminal
      I left right rightFinal hrow events w j t hvalid hwitness with
    hnot | hterminal
  · exact Or.inl hnot
  · rcases hterminal with ⟨terminal⟩
    obtain ⟨disposition, hsolved⟩ :=
      solvedTerminal_has_globalDisposition
        I left right rightFinal terminal
    exact Or.inr
      ⟨terminal.event, terminal.word, terminal.source, terminal.target,
        disposition, hsolved⟩

def BoundedResponseSemantic
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    BoundedResponseTag I left right event w j t → Unit → Prop
  | .bounded _ _ query, _ =>
      finiteGuardFormula I left right event w j t query
  | _, _ => False

def BoundedResponseTerminal
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    BoundedResponseTag I left right event w j t → Unit → Prop
  | .bounded _ _ query, _ =>
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true
  | _, _ => False

def NoBoundedResponseCompose
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (_rule :
      CompilerRule (BoundedResponseTag I left right event w j t))
    (_children : List Unit) (_witness : Unit) : Prop :=
  False

theorem boundedResponseTerminal_sound
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t) :
    BoundedResponseTerminal I left right rightFinal
        event w j t tag () ↔
      BoundedResponseSemantic I left right event w j t tag () := by
  cases tag with
  | bounded control cut query =>
      exact (finiteGuardSolver I left right rightFinal
        event w j t).correct query
  | nonstrong control cut lca macroData wire => rfl
  | strong control cut macroData wire quotient => rfl
  | hub control cut macroData wire => rfl
  | copy control cut orientation macroData wire => rfl
  | side control cut lca => rfl

theorem boundedResponse_derives_iff_terminal
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (tag : BoundedResponseTag I left right event w j t) :
    CompilerDerives
        (BoundedResponseTerminal I left right rightFinal event w j t)
        (NoBoundedResponseCompose I left right event w j t)
        tag () ↔
      BoundedResponseTerminal I left right rightFinal
        event w j t tag () := by
  constructor
  · intro hderive
    cases hderive with
    | terminal hterminal => exact hterminal
    | rule _ _ hcompose => exact False.elim hcompose
  · intro hterminal
    exact .terminal hterminal

def GlobalDispositionDerives
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventGlobalDisposition I left right event w j t → Prop
  | .inl tag =>
      CompilerDerives
        (BoundedResponseTerminal I left right rightFinal event w j t)
        (NoBoundedResponseCompose I left right event w j t)
        tag ()
  | .inr terminal =>
      decideResponsePWETerminal terminal = true

theorem globalDispositionSolved_iff_derives
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    GlobalDispositionSolved I left right rightFinal event w j t
        disposition ↔
      GlobalDispositionDerives I left right rightFinal event w j t
        disposition := by
  cases disposition with
  | inl tag =>
      rw [GlobalDispositionDerives,
        boundedResponse_derives_iff_terminal]
      cases tag <;> rfl
  | inr terminal =>
      rfl

theorem validStream_nonavoider_or_globalDerivation
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hwitness : SelectedRowWitness I left right w j t) :
    (¬ I.toSOA.Avoider (InsertionEvent.applyStream events w)) ∨
      ∃ (failedEvent : InsertionEvent α) (failedWord : Word α)
          (failedSource failedTarget : Nat),
        ∃ disposition :
            FirstEventGlobalDisposition I left right
              failedEvent failedWord failedSource failedTarget,
          GlobalDispositionDerives I left right rightFinal
            failedEvent failedWord failedSource failedTarget
            disposition := by
  rcases validStream_nonavoider_or_globalDisposition
      I left right rightFinal hrow events w j t hvalid hwitness with
    hnot | ⟨failedEvent, failedWord, failedSource, failedTarget,
      disposition, hsolved⟩
  · exact Or.inl hnot
  · exact Or.inr
      ⟨failedEvent, failedWord, failedSource, failedTarget,
        disposition,
        (globalDispositionSolved_iff_derives
          I left right rightFinal failedEvent failedWord
            failedSource failedTarget disposition).1 hsolved⟩

end NSSE
